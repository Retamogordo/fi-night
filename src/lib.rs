//! # Finite State Machine
//! Finite state machine can be considered a transformation from 2D space of {S, E} to {S}
//! where S and E are sets associated with States and Events respectively.
//! Rust provides syntax that covers this pattern:
//! ```rust,ignore
//!   let next_state =
//!     match (state, event) {
//!       (StateA, Event1) => StateB,
//!       // and generally on:
//!       //(State#i, Event#j) => State#k,
//!       (_, _) => SomeVariant
//!     };
//! ```
//! From a programmer's perspetive an FSM could be seen as a black box which reacts on Events from
//! the outer, from the machine's perspective, world, depending on its actual State.
//! These "reactions" or transitions are what is expected to be programmed once the machine template is defined.
//! This crate presents procedural macros as a trial to provide some sugar to this pattern.
//! As there is no dynamic data manipulation involved except user defined state context, each transition is supposed to be as fast as two method calls.
//! To use it include this in your code:
//! ```rust,ignore
//! #[macro_use]
//! extern crate fsm;
//! ```
//! The main macro that defines the machine's type looks like so:
//! ```rust,ignore
//! fsm!( UselessMachine [
//!   StateA on Signal1 => StateB,
//!   StateB on Signal2 => StateC,
//!   StateB on Signal3 => StateC,
//!   StateC on Signal2 => StateA,
//!   Idle on Start => StateA,
//!   _ on Reset => Idle,
//! ]);
//! ```
//! which is equivalent to more compact chained notation:
//! ```rust,ignore
//! fsm!( UselessMachine [
//!   StateA on Signal1 => StateB on (Signal2 | Signal3) => StateC on Signal2 => StateA,
//!   _ on Reset => Idle on Start => StateA
//! ]);
//! ```
//! From this declaration the macro will deduce the following:
//! ```rust,ignore
//!   pub enum UselessMachineStates {
//!     StateA,
//!     StateB,
//!     StateC,
//!     Idle,
//!   }
//! 
//!   pub enum UselessMachineSignals {
//!     Start,
//!     Reset,
//!     Signal1,
//!     Signal2,
//!     Signal3,
//!   }
//!   
//!   pub struct UselessMachine {
//!     ...
//!   }
//! ```
//! I called this machine Useless for a reason: it receives scarse information from the outer world and
//! is unable to produce coherent reactions because no user data is associated with its state.
//! The only way to obtain something useful from such a machine is by repeating matching its state.
//! 
//! Here is how a machine definition can be expanded:
//! ```rust,ignore
//!   // user data associated with state
//!  struct Count {
//!   a_count: usize,
//!   b_count: usize,
//!   other_count: usize,
//! }
//! // this will count letters only, discriminating A & B from the rest
//! // the rest of the states is introduced just for presentation purpose
//! fsm!( LetterCounter<Count> [
//!   Idle on Start => Started,
//!   _ on LetterA => IncA on Other(char) => OtherAfterA,
//!   _ on LetterB => IncB,
//!   _ on Other => IncOther,
//!   _ on (Number(u32) | Float(f64)) => NumberSt,
//!   _ on Reset => Idle,
//! ]);
//! ```
//! A struct LetterCounter with associated type Count is generated.
//! Every individual signal can carry input typed with type in parentheses.
//! (note the detail here: once Other(char) is declared, there is no need to repeat (char) in
//! declaration - will panic on type clash).
//! Now, this is not going to compile as we lack the essence - transitions, so here the second
//! part of our declaration comes - define a method for every arrow:
//! ```rust,ignore
//! // this reads: do sth when Start signal received while in Idle state
//! transition_handler!( Idle on Start for LetterCounter {
//! });
//! // this reads: do sth when LetterA signal received no matter in which actual state
//! from_any_state_transition_handler!(LetterA for LetterCounter {
//!   data.a_count += 1;
//! });
//! from_any_state_transition_handler!(LetterB for LetterCounter {
//!   data.b_count += 1;
//! });
//! from_any_state_transition_handler!(Other(char) for LetterCounter {
//!   data.other_count += 1;
//!   println!("Unrecognized counted: {}", input);
//! });
//! transition_handler!(IncA on Other(char) for LetterCounter {
//!   data.other_count += 1;
//!   println!("Unrecognized counted: {}", input);
//! });
//! from_any_state_transition_handler!(Reset for LetterCounter {
//!   data.a_count = 0;
//!   data.b_count = 0;
//!   data.other_count = 0;
//! });
//! from_any_state_transition_handler!(Number(u32) for LetterCounter {
//!   // do sth with Numbers
//! });
//! from_any_state_transition_handler!(Float(f64) for LetterCounter {
//!   // do sth with Floats
//! });
//!```
//!
//! These macros hide two references: a mutable one to data associated with state exposed by 'data',
//! and another immutable 'input' delivered with the signal.
//! 
//! As LetterCounter is a struct, you can expand its API if you want to:
//! ```rust,ignore
//! impl LetterCounter {
//!   pub fn start(&mut self) {
//!     self.signal(&Start);
//!   }
//! }
//! ```
//! LetterCounter::signal(...) method encapsulates the transition matcher.
//! ```rust,ignore
//! from_any_state_transition_handler!(Signal for Machine { ...
//! ``` 
//! is alternative for equivalent notation:
//! ```rust,ignore
//! transition_handler!(_ on Signal for Machine { ...
//! ``` 
//! 
//! Now define the instance:
//! ```rust,ignore
//! let mut counter = LetterCounter::new(Idle, Count { a_count: 0, b_count: 0, other_count: 0 });
//! ```
//! And use it:
//! ```rust,ignore
//! counter.start();
//! counter.signal(&LetterA);
//! counter.signal(&Other('x'));
//! counter.signal(&LetterA);
//! counter.signal(&LetterB);
//! counter.signal(&Number(8));
//! counter.signal(&LetterB);
//! counter.signal(&Other('x'));

//! let n = counter.data();
//! println!("counted: a -> {}, b -> {}, others -> {}", n.a_count, n.b_count, n.other_count);
//! ```
//! One can notice that in this example no code directly refers to current fsm's state 
//! (although it can be accessed via state() method).
//! I consider current state an implementation detail of machine's black box which does not
//! provide sufficient information about past, namely it does not make much sense to know what 
//! current state is out of context of some transition.  
//! There is another way to break the black box though.
//! Consider that this silly counter needs to distinguish the situation of more than 5 B letters counted
//! entering a specific state, call it MoreThan5B.
//! One could define it this way:
//! ```rust,ignore
//! Started on LetterB => IncB_1 on LetterB => IncB_2 on LetterB... and so forth.
//! ```
//! There is an alternative conditional pattern for this scenario :
//! ```rust,ignore
//!  fsm!( LetterCounter<Count> [
//!     Idle on Start => Started,
//!     _ on LetterA => IncA on Other(char) => OtherAfterA,
//!     _ on LetterB => ?,
//!     _ on Other => IncOther,
//!     _ on Reset => Idle,
//! ]);
//! ```
//! This interrogation sign declares that the LetterCounter delegates the determination of resulting
//! state to the transition handler itself.
//! And here is where this macro jumps out:
//! ```rust,ignore
//! conditional_handler!(_ on LetterB for LetterCounter {  
//!   data.b_count += 1;
//!
//!   if data.b_count < 5 {
//!     IncB
//!   } else {
//!     MoreThan5B
//!   }
//! });
//! ```
//! Now, this won't compile, the machine doesn't know what IncB and MoreThan5B are, so let's add some
//! silly transitions to our machine:
//! ```rust,ignore
//!  fsm!( LetterCounter<Count> [
//!     Idle on Start => Started on LetterB => IncB, // <-- here
//!     _ on LetterA => IncA on Other(char) => OtherAfterA,
//!      // and here
//!      MoreThan5B on LetterB => MoreThan5B,
//!     _ on LetterB => ?,
//!     _ on Other => IncOther,
//!     _ on Reset => Idle,
//! ]);
//! ```
//! and their corresponding handlers:
//! ```rust,ignore
//! transition_handler!( Started on LetterB for LetterCounter {
//!   data.b_count += 1;
//! });
//! transition_handler!( MoreThan5B on LetterB for LetterCounter {
//!  data.b_count += 1;
//!  println!("On MoreThan5B");
//! });
//! ```
//! This design defines a relaxed machine in sense that it won't change state on signal
//! no transition for which exists for current state.
//! This means this scenario is not covered:
//! ```rust,ignore
//!  fsm!( Baby [
//!     Content on GiveCandy => Content on WaitASec => Screaming,
//!     // or whatever else
//!     Content on _ => Screaming, // <-- _ won't compile
//!     // and then what ?
//!     Screaming on GiveHimCandyAnyway => Content,
//! ]);
//! ```
//! Contrary to the above General Failure or Reset scenarios are quite common:
//! ```rust,ignore
//! fsm!( SRLatch [
//!     // ...
//!     // this signal leads to failure regardless of current state
//!     _ on SLoRLo => InvalidState 
//! ]);
//! ```
//! 
//! ## meta_iter Feature
//! 
//! The crate defines a feature "meta_iter" which, when is on brings a machine's iterator into scope.
//! Note that there is no dynamic collection to iterate on, this iterator operates on metadata
//! resulting from waste product of declarations of machine's enums.
//! This feature brings a bit of text to the code and is only useful for enumerating transitions
//! while debugging, for instance.
//! The result could be then sent to a graph visualization software or just printed out.   
//! It works like so:
//! ```rust,ignore
//! let mut chains = LetterCounter::chains();
//! while let Some(mut chain) = chains.next() {
//!  while let Some(item) = chain.next() {
//!    let s = if let Some(to) = item.to {
//!        format!("{} -> {} by {}\n", item.from, to, item.on)
//!      } else {
//!        format!("{} -> {} by {}\n", item.from, "ConditionalMultichoice", item.on)   
//!      };
//!      println!("{}", s);
//!  }
//!}
//!```
//! The result of printout will be a list machine's transitions. Note that there is almost no chance
//! that the list printout coincide with yours machine layout view in source code.
//! 
//! ## fsm_gen_code Feature
//! When on this feature generates a string containing the Rust text created by the macro.
//! The string is in format of an fsm's name concatenated with _GEN_CODE identifier.
//! For example for MyMachine the string is accessed by 
//! 
//! ```rust,ignore
//! crate::MY_MACHINE_GEN_CODE 
//! ```
//! constant.
//! 
//!   
//! ## Caveats
//! 
//! Lifetime parsing for user data type is not covered, so this won't compile:
//! ```rust,ignore
//!  fsm!( LetterCounter<WithLifetime<'a>> [...]);
//! ```
//!
//! 
extern crate proc_macro;

use std::collections::{HashMap, HashSet, BinaryHeap};

use proc_macro2::{Span, TokenStream};
use syn::parse::{Parse, ParseStream, Result};
use syn::{ parse_macro_input, bracketed, parenthesized, token, Token, Ident, Type, Block, Expr, 
  GenericArgument, AngleBracketedGenericArguments, PathArguments,
};
use quote::{quote, ToTokens};
use convert_case::{Case, Casing};

#[proc_macro]
pub fn fsm(input: proc_macro::TokenStream) -> proc_macro::TokenStream  {
  #[cfg(feature = "meta_iter")]
  let mut fsm_parsed = parse_macro_input!(input as FSMParser);
  #[cfg(not(feature = "meta_iter"))]
  let fsm_parsed = parse_macro_input!(input as FSMParser);

  let state_variants: Vec<Ident> = fsm_parsed.state_enum_tokens
    .iter()
    .map(|item| item.clone())
    .collect();

  let state_enum_ident = &fsm_parsed.state_enum_ident;

  let state_enum_tokens = quote! {
    #[derive(PartialEq, Clone, Copy)]
    pub enum #state_enum_ident {
        #(#state_variants),*
      }
    use #state_enum_ident::*;
  };
  let mut output = TokenStream::from(state_enum_tokens.into_token_stream());

  let signal_variants: Vec<SignalEnumToken> = fsm_parsed.signal_enum_tokens
    .iter()
    .map(|(sig, input)| SignalEnumToken(sig.clone(), input.clone()))
    .collect();

  let signal_enum_ident = &fsm_parsed.signal_enum_ident;
  let signal_enum_tokens = quote! {
    #[derive(PartialEq, Clone)]
    pub enum #signal_enum_ident {
      #(#signal_variants),*
    }
    use #signal_enum_ident::*;
  };
  output.extend( TokenStream::from(signal_enum_tokens.into_token_stream()) );

  let quoted = quote_fsm_template(&fsm_parsed);

//  println!("{}", quoted);
 
  output.extend( TokenStream::from(quoted.into_token_stream()) );
  
  #[cfg(feature = "meta_iter")]
  {
    let quoted = quote_iter_chains(&mut fsm_parsed);

    output.extend( TokenStream::from(quoted.into_token_stream()) );
  }

  #[cfg(feature = "fsm_gen_code")]
  {
    let gen_code_const = Ident::new(
      &format!("{}_GEN_CODE", fsm_parsed.name.to_string().to_case(Case::UpperSnake)), Span::call_site());
    let gen_code = output.to_string();
    let quoted_gen_code = quote! { 
      const #gen_code_const: &str = #gen_code;
    };

    output.extend( quoted_gen_code );
  }

  output.into()
}

#[proc_macro]
pub fn transition_handler(input: proc_macro::TokenStream) -> proc_macro::TokenStream  {
  quote_transition_handler(input, HandlerSignature::Deterministic)
}

#[proc_macro]
pub fn conditional_handler(input: proc_macro::TokenStream) -> proc_macro::TokenStream  {
  quote_transition_handler(input, HandlerSignature::Conditional)
}
/*
#[proc_macro]
pub fn stackful_conditional_handler(input: proc_macro::TokenStream) -> proc_macro::TokenStream  {
  quote_transition_handler(input, HandlerSignature::Stackful)
}
*/
#[proc_macro]
pub fn from_any_state_transition_handler(input: proc_macro::TokenStream) -> proc_macro::TokenStream  {
  let mut input1 = TokenStream::from((Ident::new("_", Span::call_site())).into_token_stream());

  input1.extend(TokenStream::from((Ident::new("on", Span::call_site())).into_token_stream()));
  input1.extend(TokenStream::from(input));
  quote_transition_handler(input1.into(), HandlerSignature::Deterministic)
}

enum HandlerSignature {
  Deterministic,
  Conditional,
//  Stackful,
}

#[derive(Clone, PartialEq, Eq)]
enum StackOp {
  CompareAndPop(Expr),
  CompareAndPopIfLast(Expr),
  PeekAndCompare(Expr),
  PopAny,
  PopLastAny,
  IsEmpty,
  NotEmpty,
  None,
}

#[derive(Clone)]
enum EnumIdentAcceptingAny {
  SomeVariant(Ident),
  AnyVariant(Ident),
}

impl EnumIdentAcceptingAny {
  fn is_any(&self) -> bool {
    match self {
      Self::SomeVariant(_) => false,
      Self::AnyVariant(_) => true,
    }
  }
  fn any() -> Self {
    Self::AnyVariant(Ident::new("_", Span::call_site()))
  }
  fn unwrap_any(self) -> Ident {
//    let any_ident = Ident::new("_", Span::call_site());

    match self {
      Self::SomeVariant(var) => var,
      Self::AnyVariant(any_var) => any_var,
    }
  }
  fn unwrap_as_ref(&self) -> &Ident {
    match self {
      Self::SomeVariant(var) => var,
      Self::AnyVariant(any_var) => any_var,
    }
  }
}

impl PartialEq for EnumIdentAcceptingAny {
  fn eq(&self, other: &Self) -> bool {
    if let EnumIdentAcceptingAny::SomeVariant(st1) = self {
      if let EnumIdentAcceptingAny::SomeVariant(st2) = other {st1 == st2} else {false}
    } else {
      other.is_any()
    }
  }
}
impl Eq for EnumIdentAcceptingAny {}

#[derive(Clone, PartialEq, Eq)]
struct MatchTransitionEntry {
  from_state: EnumIdentAcceptingAny,
  signal: EnumIdentAcceptingAny,
  input: Option<Type>,
  stack_expr: StackOp,
  to_state: Option<Ident>,
}

impl std::cmp::PartialOrd for EnumIdentAcceptingAny {
  fn partial_cmp(&self, other: &Self) -> Option<std::cmp::Ordering> {
      match self {
        Self::AnyVariant(_) 
          => if other.is_any() {Some(std::cmp::Ordering::Equal)} else {Some(std::cmp::Ordering::Less)},
        Self::SomeVariant(v1) 
          => if other.is_any() {Some(std::cmp::Ordering::Greater)} else {v1.partial_cmp(other.unwrap_as_ref())},
      }  
  }
}

impl Ord for EnumIdentAcceptingAny {
  fn cmp(&self, other: &Self) -> std::cmp::Ordering {
    self.partial_cmp(other).unwrap()
  }
}

impl std::cmp::PartialOrd for StackOp {
  fn partial_cmp(&self, other: &Self) -> Option<std::cmp::Ordering> {
      match self {
        Self::None 
          => if let Self::None = other {Some(std::cmp::Ordering::Equal)} else {Some(std::cmp::Ordering::Less)},
          Self::PopAny => match other {
            Self::None => Some(std::cmp::Ordering::Greater),
            Self::PopAny => Some(std::cmp::Ordering::Equal),
            _ => Some(std::cmp::Ordering::Less),
          },
          Self::PopLastAny => match other {
            Self::None | Self::PopAny => Some(std::cmp::Ordering::Greater),
            Self::PopLastAny => Some(std::cmp::Ordering::Equal),
            _ => Some(std::cmp::Ordering::Less),
          },
          Self::IsEmpty => match other {
            Self::None | Self::PopAny | Self::PopLastAny => Some(std::cmp::Ordering::Greater),
            Self::IsEmpty => Some(std::cmp::Ordering::Equal),
            _ => Some(std::cmp::Ordering::Less),
          },
          Self::NotEmpty => match other {
            Self::None | Self::PopAny | Self::PopLastAny | Self::IsEmpty => Some(std::cmp::Ordering::Greater),
            Self::NotEmpty => Some(std::cmp::Ordering::Equal),
            _ => Some(std::cmp::Ordering::Less),
          },
          Self::CompareAndPop(_) => match other {
            Self::None | Self::PopAny | Self::PopLastAny | Self::IsEmpty | Self::NotEmpty => Some(std::cmp::Ordering::Greater),
            Self::CompareAndPop(_) => None,
            _ => Some(std::cmp::Ordering::Less),
          },
          Self::CompareAndPopIfLast(_) => match other {
            Self::CompareAndPopIfLast(_) => None,
            Self::PeekAndCompare(_) => Some(std::cmp::Ordering::Less),
            _ => Some(std::cmp::Ordering::Greater),
          },
          Self::PeekAndCompare(_) => match other {
            Self::PeekAndCompare(_) => None,
            _ => Some(std::cmp::Ordering::Greater),
          },
      }  
  }
}

impl std::cmp::PartialOrd for MatchTransitionEntry {
  fn partial_cmp(&self, other: &Self) -> Option<std::cmp::Ordering> {
    let ord_by_from_state = self.from_state.cmp(&other.from_state);
    if ord_by_from_state != std::cmp::Ordering::Equal { return Some(ord_by_from_state.reverse()); }
    let ord_by_signal = self.signal.cmp(&other.signal);
    if ord_by_signal != std::cmp::Ordering::Equal { return Some(ord_by_signal.reverse()); }
    self.stack_expr.partial_cmp(&other.stack_expr).map(|ord| ord.reverse())
//    if ord_by_stack_expr != std::cmp::Ordering::Equal { return Some(ord_by_stack_expr); }
  }
}

impl Ord for MatchTransitionEntry {
  fn cmp(&self, other: &Self) -> std::cmp::Ordering {
    if let Some(ord) = self.partial_cmp(other) {ord} else {std::cmp::Ordering::Less}
  }
}

impl ToTokens for MatchTransitionEntry {
  fn to_tokens(&self, tokens: &mut TokenStream) {
    let state = &self.from_state.unwrap_as_ref();
    let signal = &self.signal.unwrap_as_ref();
    let stack_expr = &self.stack_expr;

    let cb_token = &callback_ident(state, signal, stack_expr);
    let data_arg = quote! { &mut self.data };
    let stack_arg = quote! { &mut self.stack };
    let return_quoted = if let Some(ref to) = self.to_state {quote! {; #to}} else { quote! {} };
    let pop_match_guard 
      = match stack_expr {
        StackOp::CompareAndPop(expr) => quote! {if if let Some(val) = self.stack.last() {
          if &#expr == val { self.stack.pop(); true } else { false }
        } else {false}},
        StackOp::CompareAndPopIfLast(expr) => quote! {if if let Some(val) = self.stack.last() {
          if &#expr == val && self.stack.len() == 1 { self.stack.pop(); true } else { false }
        } else {false}},
        StackOp::PeekAndCompare(expr) => quote! {if if let Some(val) = self.stack.last() {
          { &#expr == val } } else {false}},
        StackOp::IsEmpty => quote! { if 0 == self.stack.len() },
        StackOp::NotEmpty => quote! { if 0 != self.stack.len() },
        StackOp::PopAny => quote! {if if let Some(_) = self.stack.pop() {true} else {false}},
        StackOp::PopLastAny => quote! {if 1 == self.stack.len() {self.stack.pop(); true} else {false}},
        StackOp::None => quote! {},
    }; 

    let quoted =
      if let Some(_) = self.input {
        quote! { (#state, #signal(input)) #pop_match_guard => { (Self::#cb_token)(input, #data_arg, #stack_arg) #return_quoted } } 
  
      } else {     
        quote! { (#state, #signal) #pop_match_guard  => { (Self::#cb_token)(#data_arg, #stack_arg) #return_quoted } }
      };
  
    quoted.to_tokens(tokens);
  }
}

struct SignalEnumToken(Ident, Option<Type>);

impl ToTokens for SignalEnumToken {
  fn to_tokens(&self, tokens: &mut TokenStream) {
    let sig = &self.0;
    let input = &self.1;
    let quoted;
    if let Some(input) = input {
      quoted = quote! {
        #sig(#input)
      };
    } else {
      quoted = quote! {
        #sig
      };
    }
  
    quoted.to_tokens(tokens);
  }
}

fn callback_ident(state: &Ident, signal: &Ident, stack_expr: &StackOp) -> Ident {

  let pop_expr_conv =
    match stack_expr {
      StackOp::CompareAndPop(expr) => {
        let str = &(quote!{#expr}).to_string();
        
        let re = regex::Regex::new(r"[^A-Za-z_0-9]").unwrap();
        format!("popped_{}", re.replace_all(str, "_").to_owned())
      },
      StackOp::CompareAndPopIfLast(expr) => {
        let str = &(quote!{#expr}).to_string();
        
        let re = regex::Regex::new(r"[^A-Za-z_0-9]").unwrap();
        format!("popped_last_{}", re.replace_all(str, "_").to_owned())
      },
      StackOp::PeekAndCompare(expr) => {
        let str = &(quote!{#expr}).to_string();
        
        let re = regex::Regex::new(r"[^A-Za-z_0-9]").unwrap();
        format!("peek_{}", re.replace_all(str, "_").to_owned())
      },
      StackOp::IsEmpty => "empty".to_string(),
      StackOp::NotEmpty => "notempty".to_string(),
      _ => "".to_string(),
    };
  Ident::new(
    &format!("{}_on_{}_{}", 
      state.to_string().to_case(Case::Snake),
      signal.to_string().to_case(Case::Snake),
      pop_expr_conv.to_case(Case::Snake)),
      Span::call_site()
  )
}

struct TransitionHandlerArgsParser {
  fsm_ident: Ident,
  body_item: Block,
  signature: TransitionSignature,
}

impl Parse for TransitionHandlerArgsParser {
  fn parse(input: ParseStream) -> Result<Self> {

    Ok(Self { 
      signature: input.parse()?,
      fsm_ident: { input.parse::<Token![for]>()?; input.parse()? },
      body_item: input.parse()?,
    })
  }
}

struct FSMParser {
	name: Ident,
  state_enum_ident: Ident,
  signal_enum_ident: Ident,
  data_type: Option<Type>,
  stack_sym_type: Option<Type>,
  signal_enum_tokens: HashMap<Ident, Option<Type>>,
  state_enum_tokens: HashSet<Ident>,
  match_transition_tokens: Vec<MatchTransitionEntry>,
}

impl Parse for FSMParser {
    fn parse(input: ParseStream) -> Result<Self> {
        let name: Ident = input.parse()?;
        let mut data_type: Option<Type> = None;
        let mut stack_sym_type: Option<Type> = None;
        if let Ok(type_args) = input.parse::<AngleBracketedGenericArguments>() {
          let mut args_iter = type_args.args.into_pairs();
          data_type = args_iter.next().map(|arg| match arg.into_value() {
              GenericArgument::Type(t) => t,
              _ => panic!("Type argument expected for DataItem"),
            }
          );
          stack_sym_type = args_iter.next().and_then(|arg| match arg.into_value() {
              GenericArgument::Type(t) => Some(t),
              _ => panic!("Type argument expected for StackSymbolItem"),
            }
          );
        }
        
        let state_enum_ident = Ident::new(&format!("{}{}", name.to_string(), "States"), Span::call_site());
        let signal_enum_ident = Ident::new(&format!("{}{}", name.to_string(), "Signals"), Span::call_site());
        
        let mut signal_enum_tokens = HashMap::new();
        let mut state_enum_tokens = HashSet::new();
        let mut match_transition_tokens = BinaryHeap::new();
//        let mut any_state_transition_tokens = HashMap::new();

        let content;
        bracketed!(content in input);
        let mut transition_signature: TransitionSignature = content.parse()?;
        let mut from_state;

        while !content.is_empty() {
            match transition_signature.signature_kind {
            TransitionSignatureKind::ChainJoint => {
              from_state = transition_signature.from_state.clone();

              let _: Token![=>] = content.parse()?;

              let curr_pairs = transition_signature.signals.drain(..).collect::<Vec<(EnumIdentAcceptingAny, Option<Type>)>>();

              let next_transition_signature: TransitionSignature = content.parse()?;
              let to_state = match next_transition_signature.signature_kind {
                  TransitionSignatureKind::ChainEndConditional => None, 
                  _ => Some(next_transition_signature.from_state.clone().unwrap_any()),
                };
                
              for mut pair in curr_pairs {
                let stack_expr = transition_signature.stack_expr.clone();
                let signal = pair.0.clone();
                let mut input_type = pair.1.take();  
              
                let input_type_clone = input_type.clone();
                if let EnumIdentAcceptingAny::SomeVariant(ref sig) = signal {
                  signal_enum_tokens.entry(sig.clone())
                    .and_modify(|t: &mut Option<Type>| 
                      if t.is_none() {
                        *t = input_type.clone();
                      } else {
                        if !input_type.is_none() {
//                           panic!("Signal enum variant {}(Type2) conflicts with existing variant {}(Type1). You can use empty variant {} to continue making transitions with this signal.", 
//                           sig, sig, sig);
                        } else {
                          input_type = t.clone();
                        }
                      }
                    )
                    .or_insert(input_type_clone);
                }
                match_transition_tokens.push(MatchTransitionEntry {
                  from_state: from_state.clone(),
                  signal: signal.clone(),
                  input: input_type.clone(),
                  stack_expr: stack_expr.clone(),
                  to_state: to_state.clone(),
                });

                if let EnumIdentAcceptingAny::SomeVariant(ref from) = from_state {
                  state_enum_tokens.insert(from.clone());
                }
                if let Some(ref to) = to_state {
                  state_enum_tokens.insert(to.clone());
                }
              }
              transition_signature = next_transition_signature;
            },
            TransitionSignatureKind::ChainEnd
            |
            TransitionSignatureKind::ChainEndConditional => {
              if !content.is_empty() {
                content.parse::<Token![,]>()?;
                if !content.is_empty() {
                  transition_signature = content.parse()?;
                }
              }
            },
          }
        }

        if state_enum_tokens.len() == 0 {
          panic!("Stateless State Machine ???");
        }
        let match_transition_tokens = match_transition_tokens.into_sorted_vec();
        let _quoted = quote! {
          #(#match_transition_tokens)*,
        };
//        println!("{}", _quoted);
        Ok(Self { 
          name, 
          data_type, 
          stack_sym_type,
          state_enum_ident,
          signal_enum_ident,
          signal_enum_tokens,
          state_enum_tokens,
          match_transition_tokens,
        })
    }
}

enum TransitionSignatureKind {
  ChainJoint,
  ChainEnd,
  ChainEndConditional,
}

struct TransitionSignature {
  signature_kind: TransitionSignatureKind,
  from_state: EnumIdentAcceptingAny,
  signals: Vec<(EnumIdentAcceptingAny, Option<Type>)>,
  stack_expr: StackOp,
}
impl TransitionSignature {
  fn parse_pop_token(input: &ParseStream) -> Result<StackOp> {
    let negated = input.lookahead1().peek(Token![!]);
    if negated { input.parse::<Token![!]>()?; }
    if input.lookahead1().peek(Ident) {
      let res = input.parse::<Ident>()?;
      match res.to_string().as_str()  {
        "cmp_pop_if_last" => Ok(
          if input.lookahead1().peek(Token![_]) { input.parse::<Token![_]>()?; StackOp::PopLastAny }
          else { StackOp::CompareAndPopIfLast(input.parse::<Expr>()?) }
        ),
        "cmp_pop" => Ok(
          if input.lookahead1().peek(Token![_]) { input.parse::<Token![_]>()?; StackOp::PopAny }
          else { StackOp::CompareAndPop(input.parse::<Expr>()?) }
        ),
        "peek_cmp" => Ok( StackOp::PeekAndCompare(input.parse::<Expr>()?) ),
        "pop" => Ok(StackOp::PopAny),
        "empty" => Ok(if negated {StackOp::NotEmpty} else {StackOp::IsEmpty}),
        str @ _ => panic!("Unrecognized stack operation parsed: {}", str),
      } 
    } 
    else {
      Ok(StackOp::None)
    }
  }
}

impl Parse for TransitionSignature {
  fn parse(input: ParseStream) -> Result<Self> {
    if let Ok(_) = input.parse::<Token![?]>() {
      return Ok(Self {
        signature_kind: TransitionSignatureKind::ChainEndConditional,
        from_state: EnumIdentAcceptingAny::any(),
        signals: vec![],
        stack_expr: StackOp::None,
      });
    }

    let from_state: EnumIdentAcceptingAny = if input.lookahead1().peek(Token![_]) {
      input.parse::<Token![_]>()?;

      EnumIdentAcceptingAny::any()
    } else {
      if let Ok(ty) = input.parse::<Type>() {
        match ty {
          Type::Path(path) => EnumIdentAcceptingAny::SomeVariant(path.path.segments.last().unwrap().ident.clone()),
          _ => EnumIdentAcceptingAny::SomeVariant(input.parse()?)
        }
      } else {
        EnumIdentAcceptingAny::SomeVariant(input.parse()?)
      }
    };
    
    let on_ident_parse_res = input.parse::<Ident>();
    if on_ident_parse_res.is_err() {
      if from_state.is_any() {
        panic!("Any State is not allowed as accepting state. Use ? for non-deterministic transition.");
      }
      return Ok(Self {
        from_state,
        signals: vec![],
        stack_expr: StackOp::None,
        signature_kind: TransitionSignatureKind::ChainEnd,
      });
    }

    let on_ident = on_ident_parse_res.unwrap();
    if on_ident != "on" {
      panic!("on == {}, should be 'on'", on_ident);
    }

    let mut signal: Ident;

    if input.lookahead1().peek(Token![_]) {
      input.parse::<Token![_]>()?;
      
      return Ok(Self {
        signature_kind: TransitionSignatureKind::ChainJoint,
        from_state,
        signals: vec![(EnumIdentAcceptingAny::any(), None)],
        stack_expr: Self::parse_pop_token(&input).unwrap(),
      });
    } 

    let signals_set_parsed;
    let content;
    let single_signal = 
      if input.lookahead1().peek(token::Paren) {
        parenthesized!(content in input);
        signals_set_parsed = &content;
        false
      } else { 
        signals_set_parsed = input;
        true
      };

    let mut signal_input_type: Option<Type>;
    let mut done = signals_set_parsed.is_empty();
    let mut signals = vec![];
    while !done {
      let ty = signals_set_parsed.parse::<Type>()?;
      signal = match ty {
        Type::Path(path) => {
          signal_input_type 
          = if let PathArguments::Parenthesized(args) = path.path.segments.last().unwrap().arguments.clone() {
            Some(args.inputs.first().unwrap().clone())
          } else { None };
          path.path.segments.last().unwrap().ident.clone()
        },
        _ => panic!("Not a valid signal type"),
      };
    //  println!("----------------- {} ------------------", signal);
      signals.push( (EnumIdentAcceptingAny::SomeVariant(signal), signal_input_type) );
          
      done = single_signal || signals_set_parsed.is_empty(); 
      if !done {
        signals_set_parsed.parse::<Token![|]>()?;
      }
    }
  
    return Ok(Self {
      signature_kind: TransitionSignatureKind::ChainJoint,
      from_state,
      signals,
      stack_expr: Self::parse_pop_token(&input).unwrap(),
    });

  }
}

fn quote_transition_handler(input: proc_macro::TokenStream, signature: HandlerSignature) -> proc_macro::TokenStream {
	let transition_parsed = parse_macro_input!(input as TransitionHandlerArgsParser);
  let fsm_ident = &transition_parsed.fsm_ident;
  let trait_ident = &trait_ident(fsm_ident);
  let state_ident = &transition_parsed.signature.from_state.unwrap_as_ref();
  let signal_ident = transition_parsed.signature.signals[0].0.unwrap_as_ref();
  let signal_input_type = &transition_parsed.signature.signals[0].1;
  let body_block = &transition_parsed.body_item;
  let handler_ident = &callback_ident(state_ident, signal_ident, &transition_parsed.signature.stack_expr);

  let return_type = match signature {
      HandlerSignature::Deterministic => quote! { () },
      HandlerSignature::Conditional  => quote! { <Self as #trait_ident>::StateItem },    
  };
  let input_arg = match signal_input_type {
    Some(input_type) => quote! {input: &#input_type,},
    _ => quote! {}
  };
  let tr_quoted = quote! {
    impl #fsm_ident {
      fn #handler_ident(#input_arg 
        data: &mut <Self as #trait_ident>::DataItem,
        stack: &mut Vec<<Self as #trait_ident>::StackSymbolItem>,
      ) -> #return_type
        #body_block
    }
  };
  (TokenStream::from(tr_quoted.into_token_stream())).into()
}

fn trait_ident(fsm_ident: &Ident) -> Ident {
  Ident::new(
    &format!("{}{}", fsm_ident.to_string(), "Trait"),
    Span::call_site()
  )
}

fn quote_fsm_template(parser: &FSMParser) -> TokenStream {
  let fsm_ident = &parser.name;
  let trait_ident = trait_ident(fsm_ident);
  let data_type = &parser.data_type;
  let stack_sym_type = &parser.stack_sym_type;
  let signal_enum_ident = &parser.signal_enum_ident;
  let state_enum_ident = &parser.state_enum_ident;
  let match_tr_entries = &parser.match_transition_tokens;
  let iter_item_ident = ChainIterItem::name_from_fsm(&fsm_ident);

  let mut data_method_def = quote!{};
  let mut data_mut_method_def = quote!{};
  let mut data_method_impl = quote!{};
  let mut data_mut_method_impl = quote!{};
  let mut data_arg = quote!{};
  let mut data_field_init = quote!{data: (),};

  let data_type = match data_type {
    Some(ref data_type) => {
      data_method_def = quote! { fn data(&self) -> &<Self as #trait_ident>::DataItem; };
      data_mut_method_def = quote! { fn data_mut(&mut self) -> &mut <Self as #trait_ident>::DataItem; };
      data_method_impl = quote! {
        fn data(&self) -> &<Self as #trait_ident> ::DataItem {
          &self.data
        }
      };
      data_mut_method_impl = quote! {
        fn data_mut(&mut self) -> &mut <Self as #trait_ident> ::DataItem {
          &mut self.data
        }
      };
      data_arg = quote! { data: <Self as #trait_ident>::DataItem };
      data_field_init = quote! {data,};
      quote! { #data_type }
    },
    _ => quote! { () },
  };

  let stack_sym_type = match stack_sym_type {
    Some(ref stack_sym_type) => quote! { #stack_sym_type },
    _ => quote! { () },
  };

  let quoted 
      = quote! {
        pub trait #trait_ident {
          type StateItem: PartialEq + Clone + Copy;
          type SignalItem: PartialEq;
          type DataItem;
          type StackSymbolItem: PartialEq;
          #[cfg(feature = "meta_iter")]
          type IterItem;
  
          fn signal(&mut self, signal: &Self::SignalItem);
          fn state(&self) -> &Self::StateItem;
          #data_method_def
          #data_mut_method_def
        }

        pub struct #fsm_ident {
          state: #state_enum_ident,
          data: <Self as #trait_ident>::DataItem,
          stack: Vec<<Self as #trait_ident>::StackSymbolItem>,
        }

        impl #trait_ident for #fsm_ident {
          type StateItem = #state_enum_ident;
          type SignalItem = #signal_enum_ident;
          type DataItem = #data_type;
          type StackSymbolItem = #stack_sym_type;
          #[cfg(feature = "meta_iter")]
          type IterItem = #iter_item_ident;

          fn signal(&mut self, signal: &Self::SignalItem) {
            self.state = match (self.state, signal) {
              #(#match_tr_entries),*,
              _ => self.state
            }
          }
          fn state(&self) -> &Self::StateItem {
            &self.state
          }
          #data_method_impl
          #data_mut_method_impl
        }
        impl #fsm_ident {
          pub fn new(state: #state_enum_ident, #data_arg) -> Self {
            Self { 
              state, 
              #data_field_init
              stack: vec![],
            }
          }
        }
    
      };
  let output = TokenStream::from(quoted.into_token_stream());
//  println!("{}", output);
  output
}

#[derive(Clone)]
struct ChainIterItem(Ident, Ident, Ident, Option<Ident>);

impl ChainIterItem {
  fn name(&self) -> Ident {
    Self::name_from_fsm(&self.0)
  }
  fn name_from_fsm(fsm_ident: &Ident) -> Ident {
    Ident::new( &format!("{}{}", fsm_ident, "IterItem"), Span::call_site() )
  }
  fn fsm_signal_variants_ident(fsm_ident: &Ident) -> Ident {
    let signal_enum_ident = format!("{}{}", &fsm_ident, "Signals");

    Ident::new( &format!("{}{}", &signal_enum_ident, "IterVariants"), Span::call_site() )
  }
}

impl ToTokens for ChainIterItem {
  fn to_tokens(&self, tokens: &mut TokenStream) {

    let name = self.name();
    let from = Ident::new( &format!("{}", self.1), Span::call_site() );
    let on = Ident::new( &format!("{}", self.2), Span::call_site() );
    let signal_enum_type = Self::fsm_signal_variants_ident(&self.0);
    
    let quoted = 
      match &self.3 {
        Some(to) => {
          let to = Ident::new( &format!("{}", to), Span::call_site() );
          quote! {
            #name {
              from: #from,
              on: #signal_enum_type::#on,
              to: Some(#to),
            }
          }
        },
        None => {
          quote! {
            #name {
              from: #from,
              on: #signal_enum_type::#on,
              to: None,
          }
        }
      }
    };
    quoted.to_tokens(tokens);
  }
}
struct ChainIterItemDecl(Ident, Ident, Ident, Ident);

impl ToTokens for ChainIterItemDecl {
  fn to_tokens(&self, tokens: &mut TokenStream) {

    let name = ChainIterItem::name_from_fsm(&self.0);
    let from = Ident::new( &format!("{}", self.1), Span::call_site() );
    let on = Ident::new( &format!("{}", self.2), Span::call_site() );
    let to = Ident::new( &format!("{}", self.3), Span::call_site() );
    
    let quoted = quote! {
      #name {
        from: #from,
        on: #on,
        to: Option<#to>,
      }
    };
    quoted.to_tokens(tokens);
  }
}

#[cfg(feature = "meta_iter")]
fn quote_iter_chains(fsm_parsed: &mut FSMParser) -> TokenStream {

  use std::str::FromStr;
  let fsm_ident = &fsm_parsed.name;
  let chains_ident = Ident::new( &format!("{}{}", fsm_ident, "MetaChains"), Span::call_site() );
  let iter_ident = Ident::new( &format!("{}{}", fsm_ident, "MetaIter"), Span::call_site() );
  let mut signal_variants = vec![Ident::new("ConditionalMultipleChoice", Span::call_site() )];
  signal_variants.extend( 
    fsm_parsed.signal_enum_tokens.iter().map(|(sig, _)| sig.clone()).collect::<Vec<Ident>>()
  );
  let signal_iter_variants_ident = ChainIterItem::fsm_signal_variants_ident(fsm_ident);
  
  let iter_item_decl = ChainIterItemDecl(fsm_ident.clone(), 
    fsm_parsed.state_enum_ident.clone(), signal_iter_variants_ident.clone(), fsm_parsed.state_enum_ident.clone());
  let match_tr_entries = &mut fsm_parsed.match_transition_tokens;

  let mut chains = Vec::new();
  let mut chain_lens = Vec::new();
  // expand states AnyVariant to SomeVariant collection
  while let Some(index) = match_tr_entries.iter()
    .position(|item| item.from_state.is_any()) {
      let entry = match_tr_entries.swap_remove(index);

      match_tr_entries.extend(
        fsm_parsed.state_enum_tokens.iter()
          .map(|from| {
            let mut entry = entry.clone();
            entry.from_state = EnumIdentAcceptingAny::SomeVariant(from.clone());
            entry
          })
      );
  }
  // expand signals AnyVariant to SomeVariant collection
  while let Some(index) = match_tr_entries.iter()
    .position(|item| item.signal.is_any()) {
      let entry = match_tr_entries.swap_remove(index);

      match_tr_entries.extend(
        fsm_parsed.signal_enum_tokens.iter()
          .map(|sig| {
            let mut entry = entry.clone();
            entry.signal = EnumIdentAcceptingAny::SomeVariant(sig.0.clone());
            entry
          })
      );
  }

  while let Some(mut entry) = match_tr_entries.pop() {
    let mut chain = Vec::new();

    while let Some(index) = match_tr_entries.iter()
      .position(|item| Some(item.from_state.unwrap_as_ref()) == entry.to_state.as_ref()) {

      chain.push( ChainIterItem(fsm_ident.clone(), entry.from_state.unwrap_any(), entry.signal.unwrap_any(), 
        entry.to_state.clone() ));
      entry = match_tr_entries.swap_remove(index);
    }
    chain.push( ChainIterItem(fsm_ident.clone(), entry.from_state.unwrap_any(), entry.signal.unwrap_any(), entry.to_state.clone()));

    chain_lens.push(chain.len());
    chains.extend(chain);
  }

  let chain_num = TokenStream::from_str( &chain_lens.len().to_string() ).unwrap();

  let iter_item_name = ChainIterItem::name_from_fsm(fsm_ident);
  let total_len = TokenStream::from_str( &chain_lens.iter().fold(0, |mut sum, &n| {sum += n; sum}).to_string() ).unwrap();

  let signal_iter_variants_impl_display = ImplEnumDisplay {
    variants: signal_variants.iter()
      .map(|ident| ImplEnumVariantDisplay(ident.clone()) ).collect(),
  };
  let state_enum_ident = &fsm_parsed.state_enum_ident;
  let state_enum_impl_display = ImplEnumDisplay {
    variants: fsm_parsed.state_enum_tokens.iter()
      .map(|ident| ImplEnumVariantDisplay(ident.clone()) ).collect(),
  };
  
  let quoted = quote! {
    #[derive(PartialEq, Clone, Copy)]
    pub enum #signal_iter_variants_ident {
      #(#signal_variants),*
    }
//    use #signal_iter_variants_ident::*;
      
    #[derive(Clone, Copy)]
    pub struct #iter_item_decl

    impl core::fmt::Display for #signal_iter_variants_ident {
      fn fmt(&self, f: &mut core::fmt::Formatter) -> core::fmt::Result {
        #signal_iter_variants_impl_display
      }
    }
    impl core::fmt::Display for #state_enum_ident {
      fn fmt(&self, f: &mut core::fmt::Formatter) -> core::fmt::Result {
        #state_enum_impl_display
      }
    }
    pub struct #iter_ident {
      offset: usize,
      index: usize,
      len: usize,
    }
    impl Iterator for #iter_ident {
      type Item = #iter_item_name;
      fn next(&mut self) -> Option<Self::Item> {
        if self.index < self.len { 
          let item = #chains_ident::ITEMS[self.offset + self.index];
          self.index += 1;
          Some(item)
        } else {
          None
        }
      }
    }
    pub struct #chains_ident {
      index: usize,
      offset: usize,
    }
    impl #chains_ident {
      const ITEMS: [#iter_item_name; #total_len] = [#(#chains),*,];
      const LENS: [usize; #chain_num] = [#(#chain_lens),*,];
    }
    impl Iterator for #chains_ident {
      type Item = #iter_ident;
      fn next(&mut self) -> Option<Self::Item> {
        if self.index < #chain_num { 
          let chain = #iter_ident { offset: self.offset, index: 0, len: Self::LENS[self.index] };
          self.offset += Self::LENS[self.index];
          self.index += 1;
          Some(chain)
        } else {
          None
        }
      }
    }

    impl #fsm_ident {
      pub fn chains() -> #chains_ident {
        #chains_ident { index: 0, offset: 0 }
      }
    }
  };
     
  TokenStream::from(quoted.into_token_stream())
}

struct ImplEnumDisplay {
  variants: Vec<ImplEnumVariantDisplay>,
}

impl ToTokens for ImplEnumDisplay {
  fn to_tokens(&self, tokens: &mut TokenStream) {

    let variants = &self.variants;
    let quoted = quote! { 
      match &self {
        #(#variants),*
      }
    }; 
    quoted.to_tokens(tokens);
  }
}

struct ImplEnumVariantDisplay(Ident);

impl ToTokens for ImplEnumVariantDisplay {
  fn to_tokens(&self, tokens: &mut TokenStream) {
    let variant = &self.0;
    let quoted = quote! { 
      Self::#variant => write!(f, "{}", stringify!(#variant)) 
    };
    quoted.to_tokens(tokens);
  }
}

