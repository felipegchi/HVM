use hvm_syntax::{Term, u60, Oper, Rule, File, f60};

pub mod parser;

pub fn parse_let(state: parser::State) -> parser::Answer<Option<Box<Term>>> {
  return parser::guard(
    parser::text_parser("let "),
    Box::new(|state| {
      let (state, _)    = parser::consume("let ", state)?;
      let (state, name) = parser::name1(state)?;
      let (state, _)    = parser::consume("=", state)?;
      let (state, expr) = parse_term(state)?;
      let (state, _)    = parser::text(";", state)?;
      let (state, body) = parse_term(state)?;
      Ok((state, Box::new(Term::Let { name, expr, body })))
    }),
    state,
  );
}

pub fn parse_dup(state: parser::State) -> parser::Answer<Option<Box<Term>>> {
  return parser::guard(
    parser::text_parser("dup "),
    Box::new(|state| {
      let (state, _)    = parser::consume("dup ", state)?;
      let (state, nam0) = parser::name1(state)?;
      let (state, nam1) = parser::name1(state)?;
      let (state, _)    = parser::consume("=", state)?;
      let (state, expr) = parse_term(state)?;
      let (state, _)    = parser::text(";", state)?;
      let (state, body) = parse_term(state)?;
      Ok((state, Box::new(Term::Dup { nam0, nam1, expr, body })))
    }),
    state,
  );
}

pub fn parse_sup(state: parser::State) -> parser::Answer<Option<Box<Term>>> {
  parser::guard(
    parser::text_parser("{"),
    Box::new(move |state| {
      let (state, _)    = parser::consume("{", state)?;
      let (state, val0) = parse_term(state)?;
      let (state, val1) = parse_term(state)?;
      let (state, _)    = parser::consume("}", state)?;
      Ok((state, Box::new(Term::Sup { val0, val1 })))
    }),
    state,
  )
}

pub fn parse_lam(state: parser::State) -> parser::Answer<Option<Box<Term>>> {
  let parse_symbol =
    |x| parser::parser_or(&[parser::text_parser("λ"), parser::text_parser("@")], x);
  parser::guard(
    Box::new(parse_symbol),
    Box::new(move |state| {
      let (state, _)    = parse_symbol(state)?;
      let (state, name) = parser::name(state)?;
      let (state, body) = parse_term(state)?;
      Ok((state, Box::new(Term::Lam { name, body })))
    }),
    state,
  )
}

pub fn parse_app(state: parser::State) -> parser::Answer<Option<Box<Term>>> {
  return parser::guard(
    parser::text_parser("("),
    Box::new(|state| {
      parser::list(
        parser::text_parser("("),
        parser::text_parser(""),
        parser::text_parser(")"),
        Box::new(parse_term),
        Box::new(|args| {
          if !args.is_empty() {
            args.into_iter().reduce(|a, b| Box::new(Term::App { func: a, argm: b })).unwrap()
          } else {
            Box::new(Term::U6O { numb: 0 })
          }
        }),
        state,
      )
    }),
    state,
  );
}

pub fn parse_ctr(state: parser::State) -> parser::Answer<Option<Box<Term>>> {
  parser::guard(
    Box::new(|state| {
      let (state, _) = parser::text("(", state)?;
      let (state, head) = parser::get_char(state)?;
      Ok((state, ('A'..='Z').contains(&head)))
    }),
    Box::new(|state| {
      let (state, open) = parser::text("(", state)?;
      let (state, name) = parser::name1(state)?;
      let (state, args) = if open {
        parser::until(parser::text_parser(")"), Box::new(parse_term), state)?
      } else {
        (state, Vec::new())
      };
      Ok((state, Box::new(Term::Ctr { name, args })))
    }),
    state,
  )
}

pub fn parse_num(state: parser::State) -> parser::Answer<Option<Box<Term>>> {
  parser::guard(
    Box::new(|state| {
      let (state, head) = parser::get_char(state)?;
      Ok((state, ('0'..='9').contains(&head)))
    }),
    Box::new(|state| {
      let (state, text) = parser::name1(state)?;
      if !text.is_empty() {
        if text.starts_with("0x") {
          return Ok((state, Box::new(Term::U6O { numb: u60::new(u64::from_str_radix(&text[2..], 16).unwrap()) })));
        } else if text.find(".").is_some() {
          return Ok((state, Box::new(Term::F6O { numb: f60::new(text.parse::<f64>().unwrap()) })));
        } else {
          return Ok((state, Box::new(Term::U6O { numb: u60::new(text.parse::<u64>().unwrap()) })));
        }
      } else {
        Ok((state, Box::new(Term::U6O { numb: 0 })))
      }
    }),
    state,
  )
}

pub fn parse_op2(state: parser::State) -> parser::Answer<Option<Box<Term>>> {
  fn is_op_char(chr: char) -> bool {
    matches!(chr, '+' | '-' | '*' | '/' | '%' | '&' | '|' | '^' | '<' | '>' | '=' | '!')
  }
  fn parse_oper(state: parser::State) -> parser::Answer<Oper> {
    fn op<'a>(symbol: &'static str, oper: Oper) -> parser::Parser<'a, Option<Oper>> {
      Box::new(move |state| {
        let (state, done) = parser::text(symbol, state)?;
        Ok((state, if done { Some(oper) } else { None }))
      })
    }
    parser::grammar(
      "Oper",
      &[
        op("+", Oper::Add),
        op("-", Oper::Sub),
        op("*", Oper::Mul),
        op("/", Oper::Div),
        op("%", Oper::Mod),
        op("&", Oper::And),
        op("|", Oper::Or),
        op("^", Oper::Xor),
        op("<<", Oper::Shl),
        op(">>", Oper::Shr),
        op("<=", Oper::Lte),
        op("<", Oper::Ltn),
        op("==", Oper::Eql),
        op(">=", Oper::Gte),
        op(">", Oper::Gtn),
        op("!=", Oper::Neq),
      ],
      state,
    )
  }
  parser::guard(
    Box::new(|state| {
      let (state, open) = parser::text("(", state)?;
      let (state, head) = parser::get_char(state)?;
      Ok((state, open && is_op_char(head)))
    }),
    Box::new(|state| {
      let (state, _) = parser::text("(", state)?;
      let (state, oper) = parse_oper(state)?;
      let (state, val0) = parse_term(state)?;
      let (state, val1) = parse_term(state)?;
      let (state, _) = parser::text(")", state)?;
      Ok((state, Box::new(Term::Op2 { oper, val0, val1 })))
    }),
    state,
  )
}

pub fn parse_var(state: parser::State) -> parser::Answer<Option<Box<Term>>> {
  parser::guard(
    Box::new(|state| {
      let (state, head) = parser::get_char(state)?;
      Ok((state, ('a'..='z').contains(&head) || head == '_' || head == '$'))
    }),
    Box::new(|state| {
      let (state, name) = parser::name(state)?;
      Ok((state, Box::new(Term::Var { name })))
    }),
    state,
  )
}

pub fn parse_sym_sugar(state: parser::State) -> parser::Answer<Option<Box<Term>>> {
  use std::hash::Hasher;
  parser::guard(
    parser::text_parser("%"),
    Box::new(|state| {
      let (state, _)    = parser::text("%", state)?;
      let (state, name) = parser::name(state)?;
      let hash = {
        let mut hasher = std::collections::hash_map::DefaultHasher::new();
        hasher.write(name.as_bytes());
        hasher.finish()
      };
      Ok((state, Box::new(Term::U6O { numb: hash })))
    }),
    state,
  )
}

// ask x = fn; body
// ----------------
// (fn λx body)
pub fn parse_ask_sugar_named(state: parser::State) -> parser::Answer<Option<Box<Term>>> {
  return parser::guard(
    Box::new(|state| {
      let (state, asks) = parser::text("ask ", state)?;
      let (state, name) = parser::name(state)?;
      let (state, eqls) = parser::text("=", state)?;
      Ok((state, asks && name.len() > 0 && eqls))
    }),
    Box::new(|state| {
      let (state, _)    = parser::consume("ask ", state)?;
      let (state, name) = parser::name1(state)?;
      let (state, _)    = parser::consume("=", state)?;
      let (state, func) = parse_term(state)?;
      let (state, _)    = parser::text(";", state)?;
      let (state, body) = parse_term(state)?;
      Ok((state, Box::new(Term::App { func, argm: Box::new(Term::Lam { name, body }) })))
    }),
    state,
  );
}

pub fn parse_ask_sugar_anon(state: parser::State) -> parser::Answer<Option<Box<Term>>> {
  return parser::guard(
    parser::text_parser("ask "),
    Box::new(|state| {
      let (state, _)    = parser::consume("ask ", state)?;
      let (state, func) = parse_term(state)?;
      let (state, _)    = parser::text(";", state)?;
      let (state, body) = parse_term(state)?;
      Ok((state, Box::new(Term::App { func, argm: Box::new(Term::Lam { name: "*".to_string(), body }) })))
    }),
    state,
  );
}

pub fn parse_chr_sugar(state: parser::State) -> parser::Answer<Option<Box<Term>>> {
  parser::guard(
    Box::new(|state| {
      let (state, head) = parser::get_char(state)?;
      Ok((state, head == '\''))
    }),
    Box::new(|state| {
      let (state, _) = parser::text("'", state)?;
      if let Some(c) = parser::head(state) {
        let state = parser::tail(state);
        let (state, _) = parser::text("'", state)?;
        Ok((state, Box::new(Term::U6O { numb: c as u64 })))
      } else {
        parser::expected("character", 1, state)
      }
    }),
    state,
  )
}

// TODO: parse escape sequences
pub fn parse_str_sugar(state: parser::State) -> parser::Answer<Option<Box<Term>>> {
  parser::guard(
    Box::new(|state| {
      let (state, head) = parser::get_char(state)?;
      Ok((state, head == '"' || head == '`'))
    }),
    Box::new(|state| {
      let delim = parser::head(state).unwrap_or('\0');
      let state = parser::tail(state);
      let mut chars: Vec<char> = Vec::new();
      let mut state = state;
      loop {
        if let Some(next) = parser::head(state) {
          if next == delim || next == '\0' {
            state = parser::tail(state);
            break;
          } else {
            chars.push(next);
            state = parser::tail(state);
          }
        }
      }
      let empty = Term::Ctr { name: "String.nil".to_string(), args: Vec::new() };
      let list = Box::new(chars.iter().rfold(empty, |t, h| Term::Ctr {
        name: "String.cons".to_string(),
        args: vec![Box::new(Term::U6O { numb: *h as u64 }), Box::new(t)],
      }));
      Ok((state, list))
    }),
    state,
  )
}

pub fn parse_lst_sugar(state: parser::State) -> parser::Answer<Option<Box<Term>>> {
  parser::guard(
    Box::new(|state| {
      let (state, head) = parser::get_char(state)?;
      Ok((state, head == '['))
    }),
    Box::new(|state| {
      let (state, _head) = parser::text("[", state)?;
      // let mut elems: Vec<Box<Term>> = Vec::new();
      let state = state;
      let (state, elems) = parser::until(
        Box::new(|x| parser::text("]", x)),
        Box::new(|x| {
          let (state, term) = parse_term(x)?;
          let (state, _) = parser::maybe(Box::new(|x| parser::text(",", x)), state)?;
          Ok((state, term))
        }),
        state,
      )?;
      let empty = Term::Ctr { name: "List.nil".to_string(), args: Vec::new() };
      let list = Box::new(elems.iter().rfold(empty, |t, h| Term::Ctr {
        name: "List.cons".to_string(),
        args: vec![h.clone(), Box::new(t)],
      }));
      Ok((state, list))
    }),
    state,
  )
}

pub fn parse_if_sugar(state: parser::State) -> parser::Answer<Option<Box<Term>>> {
  return parser::guard(
    parser::text_parser("if "),
    Box::new(|state| {
      let (state, _)    = parser::consume("if ", state)?;
      let (state, cond) = parse_term(state)?;
      let (state, _)    = parser::consume("{", state)?;
      let (state, if_t) = parse_term(state)?;
      let (state, _)    = parser::consume("}", state)?;
      let (state, _)    = parser::consume("else", state)?;
      let (state, _)    = parser::consume("{", state)?;
      let (state, if_f) = parse_term(state)?;
      let (state, _)    = parser::consume("}", state)?;
      Ok((state, Box::new(Term::Ctr { name: "U60.if".to_string(), args: vec![cond, if_t, if_f] })))
    }),
    state,
  );
}

pub fn parse_term(state: parser::State) -> parser::Answer<Box<Term>> {
  parser::grammar(
    "Term",
    &[
      Box::new(parse_let),
      Box::new(parse_dup),
      Box::new(parse_lam),
      Box::new(parse_ctr),
      Box::new(parse_op2),
      Box::new(parse_app),
      Box::new(parse_sup),
      Box::new(parse_num),
      Box::new(parse_sym_sugar),
      Box::new(parse_chr_sugar),
      Box::new(parse_str_sugar),
      Box::new(parse_lst_sugar),
      Box::new(parse_if_sugar),
      Box::new(parse_ask_sugar_named),
      Box::new(parse_ask_sugar_anon),
      Box::new(parse_var),
      Box::new(|state| Ok((state, None))),
    ],
    state,
  )
}

pub fn parse_rule(state: parser::State) -> parser::Answer<Option<Rule>> {
  return parser::guard(
    parser::text_parser(""),
    Box::new(|state| {
      let (state, lhs) = parse_term(state)?;
      let (state, _) = parser::consume("=", state)?;
      let (state, rhs) = parse_term(state)?;
      Ok((state, Rule { lhs, rhs }))
    }),
    state,
  );
}

pub fn parse_file(state: parser::State) -> parser::Answer<File> {
  let mut rules = Vec::new();
  let mut state = state;
  loop {
    let (new_state, done) = parser::done(state)?;
    if done {
      break;
    }
    let (new_state, rule) = parse_rule(new_state)?;
    if let Some(rule) = rule {
      rules.push(rule);
    } else {
      return parser::expected("definition", 1, state);
    }
    state = new_state;
  }

  Ok((state, File { rules }))
}

pub fn read_term(code: &str) -> Result<Box<Term>, String> {
  parser::read(Box::new(parse_term), code)
}

pub fn read_file(code: &str) -> Result<File, String> {
  parser::read(Box::new(parse_file), code)
}

#[allow(dead_code)]
pub fn read_rule(code: &str) -> Result<Option<Rule>, String> {
  parser::read(Box::new(parse_rule), code)
}