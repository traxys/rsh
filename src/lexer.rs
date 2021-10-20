use std::borrow::Cow;

use logos::Logos;

pub type Spanned<Tok, Loc, Error> = Result<(Loc, Tok, Loc), Error>;

#[derive(thiserror::Error, Debug, Clone)]
#[error("lexer error: {0}")]
pub struct LexerError(pub String);

#[derive(Debug, Clone, Logos, derive_more::Display, PartialEq)]
pub enum Token<'input> {
    #[token("let", priority = 100)]
    #[display(fmt = "let")]
    Let,
    #[token("cmd", priority = 100)]
    #[display(fmt = "cmd")]
    Cmd,
    #[token("capture", priority = 100)]
    #[display(fmt = "capture")]
    Capture,
    #[token("in", priority = 100)]
    #[display(fmt = "in")]
    In,
    #[token("int", priority = 100)]
    #[display(fmt = "int")]
    Int,
    #[token("str", priority = 100)]
    #[display(fmt = "str")]
    Str,
    #[token("any", priority = 100)]
    #[display(fmt = "any")]
    Any,
    #[token("fn", priority = 100)]
    #[display(fmt = "fn")]
    Fn,
    #[token("true", priority = 100)]
    #[display(fmt = "true")]
    True,
    #[token("false", priority = 100)]
    #[display(fmt = "false")]
    False,
    #[token("bool", priority = 100)]
    #[display(fmt = "bool")]
    Bool,
    #[token("if", priority = 100)]
    #[display(fmt = "if")]
    If,
    #[token("else", priority = 100)]
    #[display(fmt = "else")]
    Else,
    #[token("loop", priority = 100)]
    #[display(fmt = "loop")]
    Loop,
    #[token(">")]
    #[display(fmt = ">")]
    OutRedir,
    #[token("!")]
    #[display(fmt = "!")]
    Bang,
    #[token("[")]
    #[display(fmt = "[")]
    LBracket,
    #[token("]")]
    #[display(fmt = "]")]
    RBracket,
    #[token("{")]
    #[display(fmt = "{{")]
    LBrace,
    #[token("}")]
    #[display(fmt = "}}")]
    RBrace,
    #[token("<")]
    #[display(fmt = "<")]
    InRedir,
    #[token(">>")]
    #[display(fmt = ">>")]
    AppendRedir,
    #[token("(")]
    #[display(fmt = "(")]
    LParen,
    #[token(")")]
    #[display(fmt = ")")]
    RParen,
    #[token("||")]
    #[display(fmt = "||")]
    Or,
    #[token("&&")]
    #[display(fmt = "&&")]
    And,
    #[token("=")]
    #[display(fmt = "=")]
    Equal,
    #[token("=>")]
    #[display(fmt = "=>")]
    Arrow,
    #[regex("[a-zA-Z0-9_]+", priority = 10)]
    #[display(fmt = "identifier({})", _0)]
    Identifier(&'input str),
    #[regex(r"[\w\d+\-_/.$]+", callback = |lex| lex.slice())]
    #[display(fmt = "word({})", _0)]
    Word(&'input str),
    #[token("$(")]
    #[display(fmt = "$(")]
    SubShell,
    #[regex(r#"'(\\[^\n]|[^'\n])*'"#, |lex| {
        let s = lex.slice();
        escape_string(&s[1..s.len() - 1])
    })]
    #[display(fmt = "string({})", _0)]
    StrLitteral(Cow<'input, str>),
    #[regex(r#""(\\[^\n]|[^"\n])*""#, |lex| {
        let s = lex.slice();
        escape_string(&s[1..s.len() - 1])
    })]
    #[display(fmt = "istring({})", _0)]
    InterpolatedString(Cow<'input, str>),
    #[regex(r"[0-9_]+", priority = 30, callback = |lex| {
        lex
            .slice()
            .bytes()
            .filter(|&b| b != b'_')
            .fold(0, |current, digit| 10*current + (digit - b'0') as i64)
    })]
    #[display(fmt = "int({})", _0)]
    IntNum(i64),
    #[token("\n")]
    #[display(fmt = "\\n")]
    Newline,
    #[token(",")]
    #[display(fmt = ",")]
    Comma,
    #[token(";")]
    #[display(fmt = ";")]
    Semicolon,
    #[token(":")]
    #[display(fmt = ":")]
    Colon,
    #[token("|")]
    #[display(fmt = "|")]
    Pipe,
    #[error]
    #[regex(r"#[^\n]*\n", logos::skip)]
    #[regex(r"[ \t]", logos::skip)]
    #[display(fmt = "error")]
    Error,
}

fn escape_string(input: &str) -> Cow<'_, str> {
    if !input.contains('\\') {
        Cow::Borrowed(input)
    } else {
        let mut val = Vec::new();
        let mut escape = false;
        for x in input.bytes() {
            if x == b'\\' {
                escape = true;
            } else if escape {
                match x {
                    b't' => val.push(b'\t'),
                    b'n' => val.push(b'\n'),
                    _ => {
                        val.push(b'\\');
                        val.push(x);
                    }
                }
                escape = false;
            } else {
                val.push(x);
            }
        }
        Cow::Owned(String::from_utf8(val).expect("should not produce garbage"))
    }
}

pub fn lexer(input: &str) -> impl Iterator<Item = Spanned<Token<'_>, usize, LexerError>> + '_ {
    Token::lexer(input)
        .spanned()
        /* .inspect(|x| {
            dbg!(x);
        }) */
        .map(move |(token, span)| match token {
            Token::Error => Err(LexerError(format!("Unknown token: {:?}", &input[span]))),
            v => Ok((span.start, v, span.end)),
        })
}
