#![doc = include_str!("../README.md")]
#![warn(missing_docs)]
// Need this for rusty_peg
#![recursion_limit = "256"]
// I hate this lint.
#![allow(unused_parens)]
// The builtin tests don't cover the CLI and so forth, and it's just
// too darn annoying to try and make them do so.
//
// ε shows up in lalrpop/src/lr1/example/test.rs
#![cfg_attr(test, allow(dead_code, mixed_script_confusables))]
#![warn(rust_2018_idioms)]
#![deny(clippy::exit)]
#![warn(clippy::cargo)]
// This is implied by clippy::cargo, but the version overlap may happen deep in
// our dependency tree and there's little we can do about it.
#![allow(clippy::multiple_crate_versions)]

// hoist the modules that define macros up earlier
#[macro_use]
mod rust;
#[macro_use]
mod log;

mod api;
mod build;
mod collections;
mod file_text;
mod grammar;
mod kernel_set;
mod lexer;
mod lr1;
mod message;
mod normalize;
mod parser;
mod session;
mod tls;
mod tok;
mod util;

#[cfg(test)]
mod generate;
#[cfg(test)]
mod test_util;

pub use crate::api::process_root;
#[allow(deprecated)]
pub use crate::api::process_root_unconditionally;
pub use crate::api::process_src;
pub use crate::api::Configuration;
use ascii_canvas::style;


use std::fmt::Write;
use grammar::parse_tree::*;

fn abnf_syms(syms: &ExprSymbol) -> Vec<&SymbolKind> {
    fn pred(sym: &impl std::borrow::Borrow<Symbol>) -> bool {
        match &sym.borrow().kind {
            Expr(_) => true,
            AmbiguousId(_) => true,
            Terminal(_) => true,
            Nonterminal(_) => true,
            Macro(_) => true,
            Repeat(_) => true,
            Name(_, sym) | Choose(sym) => pred(sym),
            Error | Lookahead | Lookbehind => false,
        }
    }
    use SymbolKind::*;
    syms.symbols.iter().filter(pred).map(|sym| &sym.kind).collect()
}

fn abnf_len(sym: &Symbol) -> usize {
    use SymbolKind::*;
    match &sym.kind {
        Expr(e) => e.symbols.iter().map(abnf_len).sum(),
        AmbiguousId(_)
        | Terminal(_)
        | Nonterminal(_)
        | Macro(_)
        | Repeat(_) => 1,
        Name(_, sym) | Choose(sym) => abnf_len(sym),
        Error | Lookahead | Lookbehind => 0,
    }
}

fn abnf_expr(sym: &SymbolKind, out: &mut String, bounded: bool) -> std::fmt::Result {
    use SymbolKind::*;
    use TerminalString as TS;
    use RepeatOp::*;

    match sym {
        Expr(syms) => {
            abnf_paren(syms, out, bounded, |syms, out| {
                let syms = abnf_syms(syms);
                if let Some(first) = syms.first() {
                    abnf_expr(&first, out, false)?;
                }
                for rest in syms.iter().skip(1) {
                    out.push(' ');
                    abnf_expr(&rest, out, false)?;
                }
                Ok(())
            })?
        },
        AmbiguousId(id) => out.push_str(id),
        Terminal(TS::Literal(s)) => write!(out, "{s}")?,
        Terminal(TS::Bare(s)) => write!(out, "{s}")?,
        Nonterminal(name) => write!(out, "{}", name.0)?,
        Macro(ms) => {
            let one_arg = ms.args.len() == 1;
            write!(out, "{}", ms.name.0)?;
            out.push('{');
            if let Some(first) = ms.args.first() {
                abnf_expr(&first.kind, out, one_arg)?;
            }
            for rest in ms.args.iter().skip(1) {
                out.push_str(", ");
                abnf_expr(&rest.kind, out, one_arg)?;
            }
            out.push('}');
        },
        Repeat(repeat) => {
            let RepeatSymbol { op, symbol } = &**repeat;
            let mut end = "";

            match op {
                Star => out.push_str("*"),
                Plus => out.push_str("1*"),
                Question => {
                    out.push('[');
                    end = "]"
                }
            }

            abnf_expr(&symbol.kind, out, end == "]")?;

            out.push_str(end);
        },
        Name(_, sub) | Choose(sub) => {
            if abnf_len(sub) == 1 || bounded {
                abnf_expr(&sub.kind, out, bounded)?;
            } else {
                out.push('(');
                abnf_expr(&sub.kind, out, true)?;
                out.push(')');
            }
        },
        Terminal(TS::Error) | Error => out.push('!'),
        Lookahead | Lookbehind => (),
    }
    Ok(())
}

fn abnf_paren<F, R>(
    syms: &ExprSymbol,
    out: &mut String,
    bounded: bool,
    f: F,
) -> R
where
    F: FnOnce(&ExprSymbol, &mut String) -> R,
{
    let len = syms.symbols.iter().map(abnf_len).sum::<usize>();
    if len == 1 || bounded {
        f(syms, out)
    } else {
        out.push('(');
        let res = f(syms, out);
        out.push(')');
        res
    }
}

/// Parse lalrpop grammar into abnf like output
pub fn grammar_to_abnf_like(input: &str) -> String {
    let grammar = parser::parse_grammar(input).unwrap();
    let mut out = String::new();

    for item in &grammar.items {
        let GrammarItem::Nonterminal(rule) = item else { continue };
        let name = &*rule.name.0;
        let args = if rule.args.is_empty() {String::new()} else {
            let mut out = String::new();
            out.push('{');
            if let Some(first) = rule.args.first() {
                write!(out, "{}", first.0).unwrap();
            }
            for rest in rule.args.iter().skip(1) {
                out.push_str(", ");
                write!(out, "{}", rest.0).unwrap();
            }
            out.push('}');
            out
        };
        let indent = " ".repeat(name.len() + args.len() + 1);
        write!(out, "{name}{args} = ").unwrap();
        if rule.alternatives.is_empty() {
            out.push_str("()");
        }
        if let Some(first) = rule.alternatives.first() {
            let syms = abnf_syms(&first.expr);
            let alen = first.expr.symbols.iter().map(abnf_len).sum::<usize>();
            if let Some(first) = syms.first() {
                abnf_expr(&first, &mut out, alen == 1).unwrap();
            }
            for rest in syms.iter().skip(1) {
                out.push(' ');
                abnf_expr(&rest, &mut out, false).unwrap();
            }
        }
        for alt in rule.alternatives.iter().skip(1) {
            out.push('\n');
            out.push_str(&indent);
            out.push('/');

            let syms = abnf_syms(&alt.expr);
            let alen = alt.expr.symbols.iter().map(abnf_len).sum::<usize>();
            for rest in &syms {
                out.push(' ');
                abnf_expr(&rest, &mut out, alen == 1).unwrap();
            }
        }
        out.push('\n');
    }

    out
}
