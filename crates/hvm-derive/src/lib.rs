#![feature(proc_macro_span)]

//! Derive macro to generate a pre computed version
//! of a book in order to optimize it.

use std::collections::HashMap;

use proc_macro::TokenStream;
use proc_macro2::Span;
use proc_macro_error::{abort, proc_macro_error};
use syn::parse::{ParseStream, Parse};
use syn::{parse_macro_input, LitStr, Ident, Token};
use quote::quote;
use std::fs;

use hvm_runtime::rulebook::RuleBook;
use hvm_runtime::runtime;
use hvm_syntax::Rule;

struct MacroInput {
  name: Ident,
  code: LitStr
}

impl Parse for MacroInput {
  fn parse(input: ParseStream) -> syn::Result<Self> {
    let name = input.parse()?;
    input.parse::<Token![,]>()?;
    let code = input.parse()?;
    Ok(MacroInput {
      name, 
      code
    })
  }
}

fn build_name(name: &str) -> String {
  // TODO: this can still cause some name collisions.
  // Note: avoiding the use of `$` because it is not an actually valid
  // identifier character in C.
  //let name = name.replace('_', "__");
  let name = name.replace('.', "_").replace('$', "_S_");
  format!("_{}_", name)
}

fn get_var(span: Span, var: &runtime::RuleVar) -> proc_macro2::TokenStream {
  let runtime::RuleVar { param, field, erase: _ } = var;
  let param_ident = syn::Ident::new(&format!("arg{}", param), span);
  match field {
    Some(i) => {
      quote! { load_arg(ctx.heap, #param_ident, #i) }
    }
    None => {
      quote! { #param_ident }
    }
  }
}

fn build_function(
  span: Span,
  book: &RuleBook,
  fun_name: &str,
  rules: &[Rule],
) -> syn::Result<proc_macro2::TokenStream> {
  let built = runtime::build_function(book, fun_name, rules);
  if let runtime::Function::Interpreted { arity, visit, apply } = built {
    let computed_name = build_name(fun_name);

    // Generation of the visit function

    let visit_ident = syn::Ident::new(&format!("{}_visit", computed_name), span);

    let apply_body = if visit.strict_idx.is_empty() {
      quote! { return false; }
    } else {
      let mut sidx_body = Vec::new();
      for sidx in &visit.strict_idx {
        sidx_body.push(quote! {
          if !is_whnf(load_arg(ctx.heap, ctx.term, #sidx)) {
            unsafe {{ vbuf.get_unchecked(vlen) }}.store(get_loc(ctx.term, #sidx), Ordering::Relaxed);
            vlen += 1;
          }
        })
      }

      let mut visit_idx_body = Vec::new();
      for i in 0..visit.strict_idx.len() {
        visit_idx_body.push(quote! {
          if #i < vlen - 1 {
            ctx.visit.push(new_visit(unsafe {{ vbuf.get_unchecked(#i).load(Ordering::Relaxed) }}, ctx.hold, goup));
          }
        })
      }

      quote! {
        let mut vlen = 0;
        let vbuf = unsafe { ctx.heap.vbuf.get_unchecked(ctx.tid) };
        #(#sidx_body)*
        if vlen == 0 {
          return false;
        } else {
          let goup = ctx.redex.insert(ctx.tid, new_redex(*ctx.host, *ctx.cont, vlen as u64));
          #(#visit_idx_body)*
          *ctx.cont = goup;
          *ctx.host = unsafe {{ vbuf.get_unchecked(vlen - 1).load(Ordering::Relaxed) }};
          return true;
        }
      }
    };

    // Generation of the apply function

    let apply_ident = syn::Ident::new(&format!("{}_apply", computed_name), span);

    let mut strict_arguments = Vec::new();
    for i in 0..arity {
      let arg = syn::Ident::new(&format!("arg{}", i), span);
      strict_arguments.push(quote! {
        let #arg = load_arg(ctx.heap, ctx.term, #i);
      })
    }

    let mut superposition_statements = Vec::new();
    for (i, is_strict) in visit.strict_map.iter().enumerate() {
      let arg = syn::Ident::new(&format!("arg{}", i), span);
      if *is_strict {
        let i = i as u64;
        superposition_statements.push(quote! {
          if get_tag(#arg) == SUP {
            fun::superpose(ctx.heap, &ctx.prog.arit, ctx.tid, *ctx.host, ctx.term, #arg, #i);
          }
        })
      }
    }

    // For each rule condition vector
    let mut rules_statements = Vec::new();

    for (r, rule) in apply.rules.iter().enumerate() {
      let mut conditions = Vec::new();

      for (i, cond) in rule.cond.iter().enumerate() {
        let arg = syn::Ident::new(&format!("arg{}", i), span);
        let i = i as u64;

        if runtime::get_tag(*cond) == runtime::U60 {
          let num = runtime::get_num(*cond);
          conditions.push(quote! {
            (get_tag(#arg) == U60 && get_num(#arg) == #num)
          });
        }

        if runtime::get_tag(*cond) == runtime::F60 {
          let num = runtime::get_num(*cond);
          conditions.push(quote! {
            (get_tag(#arg) == F60 && get_num(#arg) == #num)
          });
        }

        if runtime::get_tag(*cond) == runtime::CTR {
          let num = runtime::get_ext(*cond);
          conditions.push(quote! {
            (get_tag(#arg) == CTR && get_ext(#arg) == #num)
          });
        }

        // If this is a strict argument, then we're in a default variable
        if runtime::get_tag(*cond) == runtime::VAR && visit.strict_map[i as usize] {
          // This is a Kind2-specific optimization. Check 'HOAS_OPT'.
          if rule.hoas && r != apply.rules.len() - 1 {
            let is_num = quote! { (get_tag(#arg) == U60 || get_tag(#arg) == F60) };
            let is_ctr = quote! { (get_tag(#arg) == CTR && arity_of(heap, #arg) == 0u) };
            let is_hoas_ctr_num = quote! { (get_tag(#arg) == CTR && get_ext(#arg) >= HOAS_CT0 && get_ext(#arg) <= HOAS_F60) };
            conditions.push(quote! {
              (#is_num || #is_ctr || #is_hoas_ctr_num)
            });
          } else {
            let is_ctr = quote! { (get_tag(#arg) == CTR) };
            let is_u60 = quote! { (get_tag(#arg) == U60) };
            let is_f60 = quote! { (get_tag(#arg) == F60) };

            conditions.push(quote! {
              (#is_ctr || #is_u60 || #is_f60)
            });
          }
        }
      }

      let condition = if conditions.is_empty() {
        quote! { true }
      } else {
        quote! {
          #(#conditions)&&*
        }
      };

      let mut function_res = Vec::new();
      let done_res = build_function_rule_rhs(span, &mut function_res, book, &rule.core, &rule.vars);

      let mut collect = Vec::new();
      for dynvar @ runtime::RuleVar { param: _, field: _, erase } in rule.vars.iter() {
        if *erase {
          let var = get_var(span, dynvar);
          collect.push(quote! {
            collect(ctx.heap, &ctx.prog.arit, ctx.tid, #var);
          })
        }
      }

      let mut clear = Vec::new();
      for (i, arity) in &rule.free {
        let arg = syn::Ident::new(&format!("arg{}", i), span);
        clear.push(quote! {
          free(ctx.heap, ctx.tid, get_loc(#arg, 0u64), #arity);
        });
      }

      let len = visit.strict_map.len() as u64;

      rules_statements.push(quote! {
        if #condition {
          inc_cost(ctx.heap, ctx.tid);
          #(#function_res)*;
          let done = #done_res;
          link(ctx.heap, *ctx.host, done);
          #(#collect)*
          #(#clear)*
          free(ctx.heap, ctx.tid, get_loc(ctx.term, 0u64), #len);
          return true;
        }
      });
    }

    let visit_fun = quote! {
      #[inline(always)]
      fn #visit_ident(ctx: ReduceCtx) -> bool {
        #apply_body
      }
    };

    let apply_fun = quote! {
      #[inline(always)]
      fn #apply_ident(ctx: ReduceCtx) -> bool {
        #(#strict_arguments)*
        #(#superposition_statements)*
        #(#rules_statements)*
        return false;
      }
    };

    Ok(quote! {
      #visit_fun
      #apply_fun
    })
  } else {
    abort!(span, "Error while parsing HVM code");
  }
}

fn build_function_rule_rhs(
  span: Span,
  code: &mut Vec<proc_macro2::TokenStream>,
  book: &RuleBook,
  term: &runtime::Core,
  vars: &[runtime::RuleVar],
) -> proc_macro2::TokenStream {
  //let statements = Vec::new();
  let mut nams = 0;

  fn fresh(nams: &mut u64, name: &str) -> String {
    let name = format!("{}_{}", name, nams);
    *nams += 1;
    name
  }

  fn alloc_lam(
    span: Span,
    code: &mut Vec<proc_macro2::TokenStream>,
    nams: &mut u64,
    lams: &mut HashMap<u64, String>,
    glob: u64,
  ) -> String {
    if let Some(got) = lams.get(&glob) {
      got.clone()
    } else {
      let name = fresh(nams, "lam");
      let name_ident = syn::Ident::new(&name, span);

      code.push(quote! { let #name_ident = alloc(ctx.heap, ctx.tid, 2u64); });

      if glob != 0 {
        // FIXME: sanitizer still can't detect if a scopeless lambda doesn't use its bound
        // variable, so we must write an Era() here. When it does, we can remove this line.
        code.push(quote! { link(heap, #name_ident + 0u64, Era()); });
        lams.insert(glob, name.clone());
      }
      name
    }
  }

  fn alloc_dup(
    span: Span,
    code: &mut Vec<proc_macro2::TokenStream>,
    nams: &mut u64,
    dups: &mut HashMap<u64, (String, String)>,
    glob: u64,
  ) -> (String, String) {
    if let Some(got) = dups.get(&glob) {
      return got.clone();
    } else {
      let coln = fresh(nams, "col");
      let name = fresh(nams, "dup");

      let coln_ident = syn::Ident::new(&coln, span);
      let name_ident = syn::Ident::new(&name, span);

      code.push(quote! { let #coln_ident = gen_dup(ctx.heap, ctx.tid); });
      code.push(quote! { let #name_ident = alloc(ctx.heap, ctx.tid, 3u64); });

      if glob != 0 {
        code.push(quote! { link(ctx.heap, #name + 0u64, Era()); });
        code.push(quote! { link(ctx.heap, #name + 1u64, Era()); });

        dups.insert(glob, (coln.clone(), name.clone()));
      }
      return (coln, name);
    }
  }

  fn build_term(
    book: &RuleBook,
    span: Span,
    code: &mut Vec<proc_macro2::TokenStream>,
    vars: &mut Vec<proc_macro2::TokenStream>,
    nams: &mut u64,
    lams: &mut HashMap<u64, String>,
    dups: &mut HashMap<u64, (String, String)>,
    term: &runtime::Core,
  ) -> proc_macro2::TokenStream {
    const INLINE_NUMBERS: bool = true;
    use hvm_runtime::Core::*;

    match term {
      Var { bidx } => {
        if *bidx < vars.len() as u64 {
          let name = vars[*bidx as usize].clone();
          quote! { #name }
        } else {
          panic!("Unbound variable.");
        }
      }
      Glo { glob, misc } => match *misc {
        runtime::VAR => {
          let name = alloc_lam(span, code, nams, lams, *glob);
          let name_ident = syn::Ident::new(&name, span);
          return quote! { Var(#name_ident) };
        }
        runtime::DP0 => {
          let (coln, name) = alloc_dup(span, code, nams, dups, *glob);
          let coln_ident = syn::Ident::new(&coln, span);
          let name_ident = syn::Ident::new(&name, span);

          return quote! { Dp0(#coln_ident, #name_ident) };
        }
        runtime::DP1 => {
          let (coln, name) = alloc_dup(span, code, nams, dups, *glob);
          let coln_ident = syn::Ident::new(&coln, span);
          let name_ident = syn::Ident::new(&name, span);

          return quote! { Dp1(#coln_ident, #name_ident) };
        }
        _ => {
          panic!("Unexpected error.");
        }
      },
      Dup { eras, glob, expr, body } => {
        let dup0 = fresh(nams, "dp0");
        let dup1 = fresh(nams, "dp1");

        let copy_ident = syn::Ident::new(&fresh(nams, "cpy"), span);
        let dup0_ident = syn::Ident::new(&dup0, span);
        let dup1_ident = syn::Ident::new(&dup1, span);

        let expr = build_term(book, span, code, vars, nams, lams, dups, expr);

        code.push(quote! { let #copy_ident = #expr; });
        code.push(quote! { let #dup0_ident; });
        code.push(quote! { let #dup1_ident; });

        let mut inside = Vec::new();

        let (coln, name) = alloc_dup(span, code, nams, dups, *glob);
        let coln_ident = syn::Ident::new(&coln, span);
        let name_ident = syn::Ident::new(&name, span);

        if eras.0 {
          inside.push(quote! { link(ctx.heap, #name_ident + 0u64, Era()); });
        }

        if eras.1 {
          inside.push(quote! { link(ctx.heap, #name_ident + 1u64, Era()); });
        }

        inside.push(quote! {
          link(ctx.heap, #name_ident + 2u64, #copy_ident);
          #dup0_ident = Dp0(#coln_ident, #name_ident);
          #dup1_ident = Dp1(#coln_ident, #name_ident);
        });

        if INLINE_NUMBERS {
          code.push(quote! {
            if get_tag(#copy_ident) == U60 || get_tag(#copy_ident) == F60 {
              inc_cost(ctx.heap, ctx.tid);
              #dup0_ident = #copy_ident;
              #dup1_ident = #copy_ident;
            } else {
              #(#inside)*;
            }
          })
        }

        vars.push(quote! { #dup0_ident });
        vars.push(quote! { #dup1_ident });
        let body = build_term(book, span, code, vars, nams, lams, dups, body);
        vars.pop();
        vars.pop();

        body
      }
      Sup { val0, val1 } => {
        let name_ident = syn::Ident::new(&fresh(nams, "sup"), span);
        let coln_ident = syn::Ident::new(&fresh(nams, "col"), span);

        let val0 = build_term(book, span, code, vars, nams, lams, dups, val0);
        let val1 = build_term(book, span, code, vars, nams, lams, dups, val1);

        code.push(quote! {
          let #coln_ident = gen_dup(ctx.heap, ctx.tid);
          let #name_ident = alloc(ctx.heap, ctx.tid, 2u64);
          link(ctx.heap, #name_ident + 0u64, #val0);
          link(ctx.heap, #name_ident + 1u64, #val1);
        });

        quote! { Sup(#coln_ident, #name_ident) }
      }
      Let { expr, body } => {
        let expr = build_term(book, span, code, vars, nams, lams, dups, expr);
        vars.push(expr);
        let body = build_term(book, span, code, vars, nams, lams, dups, body);
        vars.pop();
        body
      }
      Lam { eras, glob, body } => {
        let name = alloc_lam(span, code, nams, lams, *glob);
        let name_ident = syn::Ident::new(&name, span);

        vars.push(quote! { Var(#name_ident) });
        let body = build_term(book, span, code, vars, nams, lams, dups, body);
        vars.pop();

        if *eras {
          code.push(quote! { link(ctx.heap, #name_ident + 0u64, Era()); });
        }

        code.push(quote! { link(ctx.heap, #name_ident + 1u64, #body); });

        quote! { Lam(#name_ident) }
      }
      App { func, argm } => {
        let name = fresh(nams, "app");
        let name_ident = syn::Ident::new(&name, span);

        let func = build_term(book, span, code, vars, nams, lams, dups, func);
        let argm = build_term(book, span, code, vars, nams, lams, dups, argm);

        code.push(quote! {
          let #name_ident = alloc(ctx.heap, ctx.tid, 2u64);
          link(ctx.heap, #name_ident + 0u64, #func);
          link(ctx.heap, #name_ident + 1u64, #argm);
        });

        quote! { App(#name_ident) }
      }
      Ctr { func, args } => {
        let cargs: Vec<_> = args
          .iter()
          .map(|arg| build_term(book, span, code, vars, nams, lams, dups, arg))
          .collect();
        let name_ident = syn::Ident::new(&fresh(nams, "ctr"), span);
        let size = cargs.len() as u64;

        code.push(quote! { let #name_ident = alloc(ctx.heap, ctx.tid, #size); });

        for (i, arg) in cargs.iter().enumerate() {
          let i = i as u64;
          code.push(quote! { link(ctx.heap, #name_ident + #i, #arg); });
        }

        let fnam = build_name(book.id_to_name.get(func).unwrap_or(&format!("{}", func)));
        let fname_ident = syn::Ident::new(&fnam, span);

        quote! { Ctr(#fname_ident, #name_ident) }
      }
      Fun { func, args } => {
        let fargs: Vec<_> = args
          .iter()
          .map(|arg| build_term(book, span, code, vars, nams, lams, dups, arg))
          .collect();

        if INLINE_NUMBERS && *func == runtime::U60_IF && fargs.len() == 3 {
          let ret_ident = syn::Ident::new(&fresh(nams, "ret"), span);
          let name_ident = syn::Ident::new(&fresh(nams, "cal"), span);
          let size = fargs.len() as u64;

          let arg0 = &fargs[0];
          let arg1 = &fargs[1];
          let arg2 = &fargs[2];

          let mut links = Vec::new();

          for (i, arg) in fargs.iter().enumerate() {
            let i = i as u64;
            links.push(quote! {
              link(ctx.heap, #name_ident + #i, #arg);
            });
          }

          let fnam = build_name(book.id_to_name.get(func).unwrap_or(&format!("{}", func)));
          let fname_ident = syn::Ident::new(&fnam, span);

          code.push(quote! {
            let #ret_ident;
            if get_tag(#arg0) == U60 {
              inc_cost(ctx.heap, ctx.tid);
              if get_num(#arg0) == 0 {
                collect(ctx.heap, &ctx.prog.arit, ctx.tid, #arg1);
                #ret_ident = #arg2;
              } else {
                collect(ctx.heap, &ctx.prog.arit, ctx.tid, #arg2);
                #ret_ident = #arg1;
              }
            } else {
              let #name_ident = alloc(ctx.heap, ctx.tid, #size);
              #(#links)*
              #ret_ident = Fun(#fname_ident, #name_ident)
            }
          });

          quote! { #ret_ident }
        } else if INLINE_NUMBERS && *func == runtime::U60_SWAP && fargs.len() == 3 {
          let ret_ident = syn::Ident::new(&fresh(nams, "ret"), span);
          let both_ident = syn::Ident::new(&fresh(nams, "both"), span);
          let name_ident = syn::Ident::new(&fresh(nams, "cal"), span);

          let size = fargs.len() as u64;

          let arg0 = &fargs[0];
          let arg1 = &fargs[1];
          let arg2 = &fargs[2];

          let mut links = Vec::new();

          for (i, arg) in fargs.iter().enumerate() {
            let i = i as u64;
            links.push(quote! {
              link(ctx.heap, #name_ident + #i, #arg);
            });
          }

          let fnam = build_name(book.id_to_name.get(func).unwrap_or(&format!("{}", func)));
          let fname_ident = syn::Ident::new(&fnam, span);

          code.push(quote! {
            let #ret_ident;
            if get_tag(#arg0) == U60 {
              inc_cost(ctx.heap, ctx.tid);
              if get_num(#arg0) == 0 {
                let #both_ident = alloc(ctx.heap, ctx.tid, 2);
                link(ctx.heap, #both_ident + 0u64, #arg1);
                link(ctx.heap, #both_ident + 1u64, #arg2);
                #ret_ident = Ctr(BOTH, #both_ident);
              } else {
                let #both_ident = alloc(ctx.heap, ctx.tid, 2);
                link(ctx.heap, #both_ident + 0u64, #arg2);
                link(ctx.heap, #both_ident + 1u64, #arg1);
                #ret_ident = Ctr(BOTH, #both_ident);
              }
            } else {
              let #name_ident = alloc(ctx.heap, ctx.tid, #size);
              #(#links)*
              #ret_ident = Fun(#fname_ident, #name_ident)
            }
          });

          quote! { #ret_ident }
        } else {
          let name_ident = syn::Ident::new(&fresh(nams, "cal"), span);

          let fname = build_name(book.id_to_name.get(func).unwrap_or(&format!("{}", func)));
          let fname_ident = syn::Ident::new(&fname, span);

          let size = fargs.len() as u64;

          let mut links = Vec::new();
          for (i, arg) in fargs.iter().enumerate() {
            let i = i as u64;
            links.push(quote! {
              link(ctx.heap, #name_ident + #i, #arg);
            });
          }

          code.push(quote! {
            let #name_ident = alloc(ctx.heap, ctx.tid, #size);
            #(#links)*
          });

          quote! { Fun(#fname_ident, #name_ident) }
        }
      }
      U6O { numb } => {
        quote! { U6O (#numb) }
      }
      F6O { numb } => {
        quote! { F6O (#numb) }
      }
      Op2 { oper, val0, val1 } => {
        let retx_ident = syn::Ident::new(&fresh(nams, "ret"), span);
        let name_ident = syn::Ident::new(&fresh(nams, "op2"), span);
        let val0 = build_term(book, span, code, vars, nams, lams, dups, val0);
        let val1 = build_term(book, span, code, vars, nams, lams, dups, val1);

        code.push(quote! {
          let #retx_ident;
        });

        let op = |quoted| match *oper {
          runtime::ADD => "add",
          runtime::SUB => "sub",
          runtime::MUL => "mul",
          runtime::DIV => "div",
          runtime::MOD => if quoted { "mdl" } else { "mod" },
          runtime::AND => "and",
          runtime::OR => "or",
          runtime::XOR => "xor",
          runtime::SHL => "shl",
          runtime::SHR => "shr",
          runtime::LTN => "ltn",
          runtime::LTE => "lte",
          runtime::EQL => "eql",
          runtime::GTE => "gte",
          runtime::GTN => "gtn",
          runtime::NEQ => "neq",
          _ => panic!(),
        };

        let op_ident = syn::Ident::new(&format!("{}", op(true)), span);
        let op_name_ident = syn::Ident::new(&format!("{}", op(false).to_uppercase()), span);

        let a = quote! { get_num(#val0) };
        let b = quote! { get_num(#val1) };

        let body = quote! {
          let #name_ident = alloc(ctx.heap, ctx.tid, 2);
            link(ctx.heap, #name_ident + 0u64, #val0);
            link(ctx.heap, #name_ident + 1u64, #val1);
            #retx_ident = Op2(#op_name_ident, #name_ident);
        };

        if INLINE_NUMBERS {
          code.push(quote! {
            if get_tag(#val0) == U60 && get_tag(#val1) == U60 {
              #retx_ident = U6O(u60::#op_ident(#a, #b));
              inc_cost(ctx.heap, ctx.tid);
            } else if get_tag(#val0) == F60 && get_tag(#val1) == F60 {
              #retx_ident = U6O(f60::#op_ident(#a, #b));
              inc_cost(ctx.heap, ctx.tid);
            } else {
              #body
            }
          });
        } else {
          code.push(quote! { #body })
        }

        quote! { #retx_ident }
      }
    }
  }

  let mut vars: Vec<proc_macro2::TokenStream> = vars
    .iter()
    .map(|_var @ runtime::RuleVar { param, field, erase: _ }| {
      let arg = syn::Ident::new(&format!("arg{}", param), span);
      match field {
        Some(field) => {
          quote! { load_arg(ctx.heap, #arg, #field) }
        }
        None => {
          quote! { #arg }
        }
      }
    })
    .collect();
  let mut lams: HashMap<u64, String> = HashMap::new();
  let mut dups: HashMap<u64, (String, String)> = HashMap::new();
  build_term(book, span, code, &mut vars, &mut nams, &mut lams, &mut dups, term)
}

fn build_rulebook(const_name: Ident, book: RuleBook, span: Span) -> syn::Result<proc_macro2::TokenStream> {
  let mut id_constants = Vec::new();

  // Creates all of the constants and respective ids.
  for (id, name) in itertools::sorted(book.id_to_name.iter()) {
    let identifier = syn::Ident::new(&build_name(name), span);
    id_constants.push(quote! {
      pub const #identifier : u64 = #id;
    });
  }

  let mut constructors_constants = Vec::new();

  // Creates all of the obligatory itens of the precomputed
  // array.
  for id in itertools::sorted(book.id_to_arit.keys()) {
    if id >= &runtime::PRECOMP_COUNT {
      let name = book.id_to_name.get(id).unwrap();
      let computed_name = build_name(name);
      let arity = *book.id_to_arit.get(id).unwrap() as usize;

      let name_literal = syn::LitStr::new(name, span);

      let visit = syn::Ident::new(&format!("{}_visit", computed_name), span);
      let apply = syn::Ident::new(&format!("{}_apply", computed_name), span);

      let body = if *book.ctr_is_cal.get(name).unwrap_or(&false) {
        quote! {
          Some(PrecompFns {
            visit: #visit,
            apply: #apply
          })
        }
      } else {
        quote! { None }
      };

      let cons = quote! {
        Precomp {
          id: #id,
          name: #name_literal,
          arity: #arity,
          funcs: #body
        }
      };

      constructors_constants.push(cons)
    }
  }

  // Create all of the pre computed functions.
  let mut precomputed_functions = Vec::new();

  for id in itertools::sorted(book.id_to_arit.keys()) {
    if id >= &runtime::PRECOMP_COUNT {
      let name = book.id_to_name.get(id).unwrap();
      if let Some(rules) = book.rule_group.get(name) {
        precomputed_functions.push(build_function(span, &book, name, &rules.1)?)
      }
    }
  }

  let res = quote! {
    use crate::runtime::{*};
    use std::sync::atomic::{AtomicBool, Ordering};

    use hvm::runtime::*;
    use hvm::runtime::base::*;
    use hvm::runtime::base::precomp::*;
    use hvm::syntax::{u60, f60};

    #(#id_constants)*

    #(#precomputed_functions)*

    pub const #const_name : &[Precomp] = &[
      #(#constructors_constants),*
    ];
  };

  Ok(res)
}

// Entry point of the macro
#[proc_macro_error]
#[proc_macro]
pub fn pre_compute_hvm(input: TokenStream) -> TokenStream {
  let input: MacroInput = parse_macro_input!(input);
  let code = input.code.value();

  let file = hvm_parser::read_file(&code);

  match file {
    Ok(file) => {
      let book = hvm_runtime::rulebook::gen_rulebook(&file, &[]);
      runtime::gen_functions(&book);
      TokenStream::from(build_rulebook(input.name, book, input.code.span()).unwrap())
    }
    Err(_err) => {
      abort!(input.code.span(), "Error while parsing HVM code");
    }
  }
}


// Entry point of the macro
#[proc_macro_error]
#[proc_macro]
pub fn pre_compute_file(input: TokenStream) -> TokenStream {
  let MacroInput { name, code } = parse_macro_input!(input);

  let span = proc_macro::Span::call_site();
  let path = span.source_file().path();
  let path = path.parent().unwrap().join(code.value());

  let code = match fs::read_to_string(path.clone()) {
    Ok(res) => res,
    Err(_) => abort!(code.span(), format!("Cannot find file '{:?}'", path))
  };

  TokenStream::from(quote! { hvm::derive::pre_compute_hvm! { #name, #code }  })
}
