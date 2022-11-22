pub mod u60;
pub mod f60;

// Types
// =====

// Term
// ----

#[derive(Clone, Debug)]
pub enum Term {
  Var { name: String }, // TODO: add `global: bool`
  Dup { nam0: String, nam1: String, expr: Box<Term>, body: Box<Term> },
  Sup { val0: Box<Term>, val1: Box<Term> },
  Let { name: String, expr: Box<Term>, body: Box<Term> },
  Lam { name: String, body: Box<Term> },
  App { func: Box<Term>, argm: Box<Term> },
  Ctr { name: String, args: Vec<Box<Term>> },
  U6O { numb: u64 },
  F6O { numb: u64 },
  Op2 { oper: Oper, val0: Box<Term>, val1: Box<Term> },
}

#[derive(Clone, Copy, Debug)]
pub enum Oper {
  Add, Sub, Mul, Div,
  Mod, And, Or,  Xor,
  Shl, Shr, Lte, Ltn,
  Eql, Gte, Gtn, Neq,
}

// Rule
// ----

#[derive(Clone, Debug)]
pub struct Rule {
  pub lhs: Box<Term>,
  pub rhs: Box<Term>,
}

// File
// ----

pub struct File {
  pub rules: Vec<Rule>,
}

// Stringifier
// ===========

// Term
// ----

impl std::fmt::Display for Oper {
  fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
    write!(f, "{}", match self {
      Self::Add => "+",
      Self::Sub => "-",
      Self::Mul => "*",
      Self::Div => "/",
      Self::Mod => "%",
      Self::And => "&",
      Self::Or  => "|",
      Self::Xor => "^",
      Self::Shl => "<<",
      Self::Shr => ">>",
      Self::Lte => "<=",
      Self::Ltn => "<",
      Self::Eql => "==",
      Self::Gte => ">=",
      Self::Gtn => ">",
      Self::Neq => "!=",
    })
  }
}

impl std::fmt::Display for Term {
  // WARN: I think this could overflow, might need to rewrite it to be iterative instead of recursive?
  // NOTE: Another issue is complexity. This function is O(N^2). Should use ropes to be linear.
  fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
    fn lst_sugar(term: &Term) -> Option<String> {
      fn go(term: &Term, text: &mut String, fst: bool) -> Option<()> {
        if let Term::Ctr { name, args } = term {
          if name == "List.cons" && args.len() == 2 {
            if !fst {
              text.push_str(", ");
            }
            text.push_str(&format!("{}", args[0]));
            go(&args[1], text, false)?;
            return Some(());
          }
          if name == "List.nil" && args.is_empty() {
            return Some(());
          }
        }
        None
      }
      let mut result = String::new();
      result.push('[');
      go(term, &mut result, true)?;
      result.push(']');
      Some(result)
    }

    fn str_sugar(term: &Term) -> Option<String> {
      fn go(term: &Term, text: &mut String) -> Option<()> {
        if let Term::Ctr { name, args } = term {
          if name == "String.cons" && args.len() == 2 {
            if let Term::U6O { numb } = *args[0] {
              text.push(std::char::from_u32(numb as u32)?);
              go(&args[1], text)?;
              return Some(());
            }
          }
          if name == "String.nil" && args.is_empty() {
            return Some(());
          }
        }
        None
      }
      let mut result = String::new();
      result.push('"');
      go(term, &mut result)?;
      result.push('"');
      Some(result)
    }
    match self {
      Self::Var { name } => write!(f, "{}", name),
      Self::Dup { nam0, nam1, expr, body } => write!(f, "dup {} {} = {}; {}", nam0, nam1, expr, body),
      Self::Sup { val0, val1 } => write!(f, "{{{} {}}}", val0, val1),
      Self::Let { name, expr, body } => write!(f, "let {} = {}; {}", name, expr, body),
      Self::Lam { name, body } => write!(f, "λ{} {}", name, body),
      Self::App { func, argm } => {
        let mut args = vec![argm];
        let mut expr = func;
        while let Self::App { func, argm } = &**expr {
          args.push(argm);
          expr = func;
        }
        args.reverse();
        write!(f, "({} {})", expr, args.iter().map(|x| format!("{}",x)).collect::<Vec<String>>().join(" "))
      },
      Self::Ctr { name, args } => {
        // Ctr sugars
        let sugars = [str_sugar, lst_sugar];
        for sugar in sugars {
          if let Some(term) = sugar(self) {
            return write!(f, "{}", term);
          }
        }

        write!(f, "({}{})", name, args.iter().map(|x| format!(" {}", x)).collect::<String>())
      }
      Self::U6O { numb } => write!(f, "{}", &u60::show(*numb)),
      Self::F6O { numb } => write!(f, "{}", &f60::show(*numb)),
      Self::Op2 { oper, val0, val1 } => write!(f, "({} {} {})", oper, val0, val1),
    }
  }
}

// Rule
// ----

impl std::fmt::Display for Rule {
  fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
    write!(f, "{} = {}", self.lhs, self.rhs)
  }
}

// File
// ----

impl std::fmt::Display for File {
  fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
    write!(f, "{}", self.rules.iter().map(|rule| format!("{}", rule)).collect::<Vec<String>>().join("\n"))
  }
}