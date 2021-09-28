use ansi_term::Color;
use lazy_static::lazy_static;
use rustyline::{highlight::Highlighter as HiTrait, Helper};
use rustyline_derive::{Completer, Hinter, Validator};
use serde::{ser::SerializeMap, Deserialize, Deserializer, Serialize, Serializer};
use serde_json::json;
use std::{cell::RefCell, collections::HashMap, fmt::Write, path::Path};
use tree_sitter_highlight::{HighlightConfiguration, HighlightEvent, Highlighter};

const HIGHLGHTS_NAMES: &[&str] = &[
    "attribute",
    "constant",
    "function.builtin",
    "function",
    "keyword",
    "operator",
    "property",
    "punctuation",
    "punctuation.bracket",
    "punctuation.delimiter",
    "string",
    "string.special",
    "tag",
    "type",
    "type.builtin",
    "variable",
    "variable.builtin",
    "variable.parameter",
];

lazy_static! {
    static ref CSS_STYLES_BY_COLOR_ID: Vec<String> =
        serde_json::from_str(include_str!("../vendor/xterm-colors.json")).unwrap();
}

#[derive(Debug, Default)]
pub struct Style {
    pub ansi: ansi_term::Style,
    pub css: Option<String>,
}

#[derive(Debug)]
pub struct Theme {
    pub styles: Vec<Style>,
    pub highlight_names: Vec<String>,
}

#[derive(Default, Deserialize, Serialize)]
pub struct ThemeConfig {
    #[serde(default)]
    pub theme: Theme,
}

impl Theme {
    pub fn load(path: &Path) -> std::io::Result<Self> {
        let json = std::fs::read_to_string(path)?;
        Ok(serde_json::from_str(&json).unwrap_or_default())
    }

    pub fn default_style(&self) -> Style {
        Style::default()
    }
}

impl<'de> Deserialize<'de> for Theme {
    fn deserialize<D>(deserializer: D) -> std::result::Result<Theme, D::Error>
    where
        D: Deserializer<'de>,
    {
        let mut styles = Vec::new();
        let mut highlight_names = Vec::new();
        if let Ok(colors) = HashMap::<String, serde_json::Value>::deserialize(deserializer) {
            highlight_names.reserve(colors.len());
            styles.reserve(colors.len());
            for (name, style_value) in colors {
                let mut style = Style::default();
                parse_style(&mut style, style_value);
                highlight_names.push(name);
                styles.push(style);
            }
        }
        Ok(Self {
            styles,
            highlight_names,
        })
    }
}

impl Serialize for Theme {
    fn serialize<S>(&self, serializer: S) -> std::result::Result<S::Ok, S::Error>
    where
        S: Serializer,
    {
        let mut map = serializer.serialize_map(Some(self.styles.len()))?;
        for (name, style) in self.highlight_names.iter().zip(&self.styles) {
            let style = &style.ansi;
            let color = style.foreground.map(|color| match color {
                Color::Black => json!("black"),
                Color::Blue => json!("blue"),
                Color::Cyan => json!("cyan"),
                Color::Green => json!("green"),
                Color::Purple => json!("purple"),
                Color::Red => json!("red"),
                Color::White => json!("white"),
                Color::Yellow => json!("yellow"),
                Color::RGB(r, g, b) => json!(format!("#{:x?}{:x?}{:x?}", r, g, b)),
                Color::Fixed(n) => json!(n),
            });
            if style.is_bold || style.is_italic || style.is_underline {
                let mut style_json = HashMap::new();
                if let Some(color) = color {
                    style_json.insert("color", color);
                }
                if style.is_bold {
                    style_json.insert("bold", serde_json::Value::Bool(true));
                }
                if style.is_italic {
                    style_json.insert("italic", serde_json::Value::Bool(true));
                }
                if style.is_underline {
                    style_json.insert("underline", serde_json::Value::Bool(true));
                }
                map.serialize_entry(&name, &style_json)?;
            } else if let Some(color) = color {
                map.serialize_entry(&name, &color)?;
            } else {
                map.serialize_entry(&name, &serde_json::Value::Null)?;
            }
        }
        map.end()
    }
}

impl Default for Theme {
    fn default() -> Self {
        serde_json::from_str(
            r#"
            {
              "attribute": {"color": 124, "italic": true},
              "comment": {"color": 245, "italic": true},
              "constant.builtin": {"color": 94, "bold": true},
              "constant": 94,
              "constructor": 136,
              "embedded": null,
              "function.builtin": {"color": 26, "bold": true},
              "function": 26,
              "keyword": 56,
              "number": {"color": 94, "bold": true},
              "property": 124,
              "operator": {"color": 239, "bold": true},
              "punctuation.bracket": 239,
              "punctuation.delimiter": 239,
              "string.special": 30,
              "string": 28,
              "tag": 18,
              "type": 23,
              "type.builtin": {"color": 23, "bold": true},
              "variable.builtin": {"bold": true},
              "variable.parameter": {"underline": true}
            }
            "#,
        )
        .unwrap()
    }
}

fn parse_style(style: &mut Style, json: serde_json::Value) {
    use serde_json::Value;

    if let Value::Object(entries) = json {
        for (property_name, value) in entries {
            match property_name.as_str() {
                "bold" => {
                    if value == Value::Bool(true) {
                        style.ansi = style.ansi.bold()
                    }
                }
                "italic" => {
                    if value == Value::Bool(true) {
                        style.ansi = style.ansi.italic()
                    }
                }
                "underline" => {
                    if value == Value::Bool(true) {
                        style.ansi = style.ansi.underline()
                    }
                }
                "color" => {
                    if let Some(color) = parse_color(value) {
                        style.ansi = style.ansi.fg(color);
                    }
                }
                _ => {}
            }
        }
        style.css = Some(style_to_css(style.ansi));
    } else if let Some(color) = parse_color(json) {
        style.ansi = style.ansi.fg(color);
        style.css = Some(style_to_css(style.ansi));
    } else {
        style.css = None;
    }

    if let Some(Color::RGB(red, green, blue)) = style.ansi.foreground {
        if !terminal_supports_truecolor() {
            style.ansi = style.ansi.fg(closest_xterm_color(red, green, blue));
        }
    }
}

fn terminal_supports_truecolor() -> bool {
    use std::env;

    if let Ok(truecolor) = env::var("COLORTERM") {
        truecolor == "truecolor" || truecolor == "24bit"
    } else {
        false
    }
}

fn closest_xterm_color(red: u8, green: u8, blue: u8) -> Color {
    use std::cmp::{max, min};

    let colors = CSS_STYLES_BY_COLOR_ID
        .iter()
        .enumerate()
        .map(|(color_id, hex)| (color_id as u8, hex_string_to_rgb(hex).unwrap()));

    // Get the xterm color with the minimum Euclidean distance to the target color
    // i.e.  distance = √ (r2 - r1)² + (g2 - g1)² + (b2 - b1)²
    let distances = colors.map(|(color_id, (r, g, b))| {
        let r_delta: u32 = (max(r, red) - min(r, red)).into();
        let g_delta: u32 = (max(g, green) - min(g, green)).into();
        let b_delta: u32 = (max(b, blue) - min(b, blue)).into();
        let distance = r_delta.pow(2) + g_delta.pow(2) + b_delta.pow(2);
        // don't need to actually take the square root for the sake of comparison
        (color_id, distance)
    });

    Color::Fixed(distances.min_by(|(_, d1), (_, d2)| d1.cmp(d2)).unwrap().0)
}

fn parse_color(json: serde_json::Value) -> Option<Color> {
    use serde_json::Value;

    match json {
        Value::Number(n) => match n.as_u64() {
            Some(n) => Some(Color::Fixed(n as u8)),
            _ => None,
        },
        Value::String(s) => match s.to_lowercase().as_str() {
            "black" => Some(Color::Black),
            "blue" => Some(Color::Blue),
            "cyan" => Some(Color::Cyan),
            "green" => Some(Color::Green),
            "purple" => Some(Color::Purple),
            "red" => Some(Color::Red),
            "white" => Some(Color::White),
            "yellow" => Some(Color::Yellow),
            s => {
                if let Some((red, green, blue)) = hex_string_to_rgb(&s) {
                    Some(Color::RGB(red, green, blue))
                } else {
                    None
                }
            }
        },
        _ => None,
    }
}

fn hex_string_to_rgb(s: &str) -> Option<(u8, u8, u8)> {
    if s.starts_with("#") && s.len() >= 7 {
        if let (Ok(red), Ok(green), Ok(blue)) = (
            u8::from_str_radix(&s[1..3], 16),
            u8::from_str_radix(&s[3..5], 16),
            u8::from_str_radix(&s[5..7], 16),
        ) {
            Some((red, green, blue))
        } else {
            None
        }
    } else {
        None
    }
}

fn style_to_css(style: ansi_term::Style) -> String {
    let mut result = "style='".to_string();
    if style.is_underline {
        write!(&mut result, "text-decoration: underline;").unwrap();
    }
    if style.is_bold {
        write!(&mut result, "font-weight: bold;").unwrap();
    }
    if style.is_italic {
        write!(&mut result, "font-style: italic;").unwrap();
    }
    if let Some(color) = style.foreground {
        write_color(&mut result, color);
    }
    result.push('\'');
    result
}

fn write_color(buffer: &mut String, color: Color) {
    if let Color::RGB(r, g, b) = &color {
        write!(buffer, "color: #{:x?}{:x?}{:x?}", r, g, b).unwrap()
    } else {
        write!(
            buffer,
            "color: {}",
            match color {
                Color::Black => "black",
                Color::Blue => "blue",
                Color::Red => "red",
                Color::Green => "green",
                Color::Yellow => "yellow",
                Color::Cyan => "cyan",
                Color::Purple => "purple",
                Color::White => "white",
                Color::Fixed(n) => CSS_STYLES_BY_COLOR_ID[n as usize].as_str(),
                Color::RGB(_, _, _) => unreachable!(),
            }
        )
        .unwrap()
    }
}

#[derive(Completer, Hinter, Validator)]
pub(crate) struct Editor {
    hi: RefCell<Highlighter>,
    hi_cfg: HighlightConfiguration,
    hi_theme: Theme,
}

impl Editor {
    pub fn new() -> Self {
        let mut hi_cfg = HighlightConfiguration::new(
            tree_sitter_rsh::language(),
            tree_sitter_rsh::HIGHLIGHTS_QUERY,
            "",
            "",
        )
        .expect("Could not init tree sitter");
        hi_cfg.configure(HIGHLGHTS_NAMES);
        dbg!(tree_sitter_rsh::HIGHLIGHTS_QUERY);
        Editor {
            hi: RefCell::new(Highlighter::new()),
            hi_cfg,
            hi_theme: Default::default(),
        }
    }
}

impl HiTrait for Editor {
    fn highlight<'l>(&self, line: &'l str, pos: usize) -> std::borrow::Cow<'l, str> {
        let mut hi = self.hi.borrow_mut();
        let events = hi
            .highlight(&self.hi_cfg, line.as_bytes(), None, |_| None)
            .expect("hi failed");

        let mut s = Vec::new();

        let mut style_stack = vec![self.hi_theme.default_style().ansi];
        for event in events {
            match event.expect("hi failure") {
                HighlightEvent::HighlightStart(kind) => {
                    style_stack.push(self.hi_theme.styles[kind.0].ansi);
                }
                HighlightEvent::HighlightEnd => {
                    style_stack.pop();
                }
                HighlightEvent::Source { start, end } => {
                    style_stack
                        .last()
                        .unwrap()
                        .paint(&line.as_bytes()[start..end])
                        .write_to(&mut s)
                        .expect("can fail write in string?");
                }
            }
        }

        let s = String::from_utf8(s).expect("we got UTF-8 in, hi is UTF8");

        s.into()
    }

    fn highlight_char(&self, _line: &str, _pos: usize) -> bool {
        true
    }
}

impl Helper for Editor {}
