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
//!       (_, _) => SomeState
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
//! ## Caveats
//! 
//! Lifetime parsing for user data type is not covered, so this won't compile:
//! ```rust,ignore
//!  fsm!( LetterCounter<WithLifetime<'a>> [...]);
//! ```
//!
//! 
extern crate proc_macro;

use std::collections::{HashMap, HashSet};

use proc_macro2::{Span, TokenStream};
use syn::parse::{Parse, ParseStream, Result};
use syn::{ parse_macro_input, bracketed, parenthesized, token, Token, Ident, Type, Block, 
  GenericArgument, AngleBracketedGenericArguments,
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
 
  output.extend( TokenStream::from(quoted.into_token_stream()) );
  
  #[cfg(feature = "meta_iter")]
  {
  let quoted = quote_iter_chains(&mut fsm_parsed);

  output.extend( TokenStream::from(quoted.into_token_stream()) );
  }

  output.into()
}

#[proc_macro]
pub fn transition_handler(input: proc_macro::TokenStream) -> proc_macro::TokenStream  {
  quote_transition_handler(input, false)
}

#[proc_macro]
pub fn conditional_handler(input: proc_macro::TokenStream) -> proc_macro::TokenStream  {
  quote_transition_handler(input, true)
}

#[proc_macro]
pub fn from_any_state_transition_handler(input: proc_macro::TokenStream) -> proc_macro::TokenStream  {
  let mut input1 = TokenStream::from((Ident::new("_", Span::call_site())).into_token_stream());

  input1.extend(TokenStream::from((Ident::new("on", Span::call_site())).into_token_stream()));
  input1.extend(TokenStream::from(input));
  quote_transition_handler(input1.into(), false)
}

#[derive(Clone)]
enum StateOption {
  SomeState(Ident),
  AnyState,
}

impl StateOption {
  fn into_option(self) -> Option<Ident> {
    match self {
      Self::SomeState(state) => Some(state),
      Self::AnyState => None,
    }
  }
  #[allow(dead_code)]
  fn as_option(&self) -> Option<&Ident> {
    match self {
      Self::SomeState(ref state) => Some(state),
      Self::AnyState => None,
    }
  }
}

#[derive(PartialEq, Eq, Hash)]
struct StateSignalToken(Ident, Ident);

#[derive(Clone)]
struct MatchTransitionEntry(StateOption, Ident, Option<Type>, Option<Ident>, bool);

impl ToTokens for MatchTransitionEntry {
  fn to_tokens(&self, tokens: &mut TokenStream) {
    let any_state_ident = Ident::new("_", Span::call_site());
    let state = match self.0 {
      StateOption::SomeState(ref state) => state,
      StateOption::AnyState => &any_state_ident,
    };
    let signal = &self.1;
    let input = &self.2;
    let to_state = &self.3;
    let with_data = self.4;

    let cb_token = callback_ident(state, signal);

    let quoted =
      if let Some(_) = input {
        if with_data {
          if let Some(to) = to_state {
            quote! { (#state, #signal(input)) => { (Self::#cb_token)(input, &mut self.data); #to } } 
          } else {
            quote! { (#state, #signal(input)) => { (Self::#cb_token)(input, &mut self.data) } } 
          }
        } else {
           if let Some(to) = to_state {
            quote! { (#state, #signal(input)) => { (Self::#cb_token)(input, &mut ()); #to } } 
          } else {
            quote! { (#state, #signal(input)) => { (Self::#cb_token)(input, &mut ()) } } 
          }
        }
  
      } else {     
          if with_data {
            if let Some(to) = to_state {
              quote! { (#state, #signal) => { (Self::#cb_token)(&mut self.data); #to } }
            } else {
              quote! { (#state, #signal) => { (Self::#cb_token)(&mut self.data) } }
            }
  
          } else {
            if let Some(to) = to_state {
              quote! { (#state, #signal) => { (Self::#cb_token)(&mut ()); #to } }
            } else {
              quote! { (#state, #signal) => { (Self::#cb_token)(&mut ()) } }
            }
          }
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

fn callback_ident(state: &Ident, signal: &Ident) -> Ident {
  Ident::new(
    &format!("{}_on_{}", 
      state.to_string().to_case(Case::Snake),
      signal.to_string().to_case(Case::Snake)),
      Span::call_site()
  )
}

struct TransitionHandlerArgsParser {
  fsm_ident: Ident,
  body_item: Block,
  state_signal_pair: StateSignalPair,
}

impl Parse for TransitionHandlerArgsParser {
  fn parse(input: ParseStream) -> Result<Self> {

    match input.parse()? {
      StateSignalPairParser::ChainJoint(state_signal_pairs)
      |
      StateSignalPairParser::FromAnyStateChainStart(state_signal_pairs) => {
        if state_signal_pairs.len() > 1 {
          panic!("Only one signal variant must be used for transition signature");
        }

        let state_signal_pair = state_signal_pairs[0].clone();
        let _: Token![for] = input.parse()?;
        let fsm_ident: Ident = input.parse()?;
        
        let body_item: Block = input.parse()?;
    
        Ok(Self { 
          state_signal_pair,
          fsm_ident,
          body_item,
        })
      },
      _ => {
        panic!("Invalid transition");
      }
    }
  }
}

struct FSMParser {
	name: Ident,
  state_enum_ident: Ident,
  signal_enum_ident: Ident,
  data_type: Option<Type>,
//  transition_tokens: HashMap<StateSignalToken, Option<Ident>>,
//  any_state_transition_tokens: HashMap<Ident, Option<Ident>>,
  signal_enum_tokens: HashMap<Ident, Option<Type>>,
  state_enum_tokens: HashSet<Ident>,
  match_transition_tokens: Vec<MatchTransitionEntry>,
}

impl Parse for FSMParser {
    fn parse(input: ParseStream) -> Result<Self> {
        let name: Ident = input.parse()?;
        let mut data_type: Option<Type> = None;
        if let Ok(mut type_arg) = input.parse::<AngleBracketedGenericArguments>() {
          data_type = Some(
            match type_arg.args.pop().unwrap().into_value() {
              GenericArgument::Type(t) => t,
              _ => panic!("Not a type"),
            }
          );
        }
        
        let state_enum_ident = Ident::new(&format!("{}{}", name.to_string(), "States"), Span::call_site());
        let signal_enum_ident = Ident::new(&format!("{}{}", name.to_string(), "Signals"), Span::call_site());
        
        let mut signal_enum_tokens = HashMap::new();
        let mut state_enum_tokens = HashSet::new();
        let mut transition_tokens = HashMap::new();
        let mut any_state_transition_tokens = HashMap::new();

        let content;
        bracketed!(content in input);

        let mut pair_parser: StateSignalPairParser = content.parse()?;
        
        while !content.is_empty() {
          match pair_parser {
            StateSignalPairParser::ChainJoint(ref mut pairs) => {

                let _: Token![=>] = content.parse()?;

                let from_state = pairs[0].from_state.clone();
                let curr_pairs = pairs.drain(..).collect::<Vec<StateSignalPair>>();

                pair_parser = content.parse()?;
                let to_state = match pair_parser {
                  StateSignalPairParser::ChainJoint(ref mut next_pairs) => next_pairs[0].from_state.clone(),
                  StateSignalPairParser::ChainEnd(ref mut state) => Some(state.clone()),
                  StateSignalPairParser::ConditionalTransition => None,
                  StateSignalPairParser::FromAnyStateChainStart(_) => panic!("AnyState pattern is allowed only at start of transition chain"),
                };

                for mut pair in curr_pairs {
                  let signal = pair.signal.0.clone();
                  let input_type = pair.signal.1.take();  
                  let state_signal_token = StateSignalToken(from_state.clone().unwrap(), signal.clone());       

                  if transition_tokens.get(&state_signal_token).is_none() {
                      transition_tokens.insert(state_signal_token, to_state.clone());
                  } else {
                    panic!("({}, {}) conflicts with existing transition.", from_state.unwrap(), signal)
                  }
                
                  let input_type_clone = input_type.clone();
                  signal_enum_tokens.entry(signal.clone())
                    .and_modify(|t: &mut Option<Type>| 
                      if t.is_none() {
                        *t = input_type;
                      } else {
                        if !input_type.is_none() {
                          panic!("Signal enum variant {}(Type2) conflicts with existing variant {}(Type1). You can use empty variant {} to continue making transitions with this signal.", 
                          signal, signal, signal);
                        }
                      }
                    )
                    .or_insert(input_type_clone);
                  state_enum_tokens.insert(from_state.clone().unwrap());
                  if let Some(to) = to_state.clone() {
                    state_enum_tokens.insert(to);
                  }
                }
            },
            StateSignalPairParser::FromAnyStateChainStart(ref mut pairs) => {
              let _: Token![=>] = content.parse()?;

              let curr_pairs = pairs.drain(..).collect::<Vec<StateSignalPair>>();

              pair_parser = content.parse()?;
              let to_state = match pair_parser {
                StateSignalPairParser::ChainJoint(ref mut next_pairs) => next_pairs[0].from_state.clone(),
                StateSignalPairParser::ChainEnd(ref mut state) => Some(state.clone()),
                StateSignalPairParser::ConditionalTransition => None,
                StateSignalPairParser::FromAnyStateChainStart(_) => panic!("AnyState pattern is allowed only at start of transition chain"),
              };

              for mut pair in curr_pairs {
                let signal = pair.signal.0.clone();
                let input_type = pair.signal.1.take();  

                if any_state_transition_tokens.get(&signal).is_none() {
                  any_state_transition_tokens.insert(signal.clone(), to_state.clone());
                } else {
                  panic!("(_, {}) conflicts with existing transition.", signal)
                }
              
                let input_type_clone = input_type.clone();
                signal_enum_tokens.entry(signal.clone())
                  .and_modify(|t: &mut Option<Type>| 
                    if t.is_none() {
                      *t = input_type;
                    } else {
                      if !input_type.is_none() {
                        panic!("Signal enum variant {}(Type2) conflicts with existing variant {}(Type1). You can use empty variant {} to continue making transitions with this signal.", 
                        signal, signal, signal);
                      }
                    }
                  )
                  .or_insert(input_type_clone);
                if let Some(to) = to_state.clone() {
                  state_enum_tokens.insert(to);
                }
              }
            },

            StateSignalPairParser::ChainEnd(_)
            |
            StateSignalPairParser::ConditionalTransition => {
                if !content.is_empty() {
                  content.parse::<Token![,]>()?;
                if !content.is_empty() {
                  pair_parser = content.parse()?;
                }
              }
            },
          }
        }

        if state_enum_tokens.len() == 0 {
          panic!("Stateless State Machine ???");
        }

        let mut match_transition_tokens = transition_tokens.iter()
        .map(|(state_signal, to_state)| 
          MatchTransitionEntry(
            StateOption::SomeState(state_signal.0.clone()), 
            state_signal.1.clone(), 
            signal_enum_tokens.get(&state_signal.1).unwrap().clone(),
            to_state.clone(),
            data_type.is_some()),
        )
        .collect::<Vec<MatchTransitionEntry>>();
        match_transition_tokens.extend( 
          any_state_transition_tokens.iter()
          .map(|(signal, to_state)| 
            MatchTransitionEntry(
              StateOption::AnyState, 
              signal.clone(), 
              signal_enum_tokens.get(&signal).unwrap().clone(),
              to_state.clone(),
              data_type.is_some()),
          )
          .collect::<Vec<MatchTransitionEntry>>()
        );
    

        Ok(Self { 
          name, 
          data_type, 
          state_enum_ident,
          signal_enum_ident,
          signal_enum_tokens,
          state_enum_tokens,
//          transition_tokens,
//          any_state_transition_tokens,
          match_transition_tokens,
         })
    }
}
#[derive(Clone)]
struct StateSignalPair {
  from_state: Option<Ident>,
  signal: (Ident, Option<Type>),
//  signal_input_type: Option<Type>,
}

enum StateSignalPairParser {
  ChainEnd(Ident),
  ChainJoint(Vec<StateSignalPair>),
  FromAnyStateChainStart(Vec<StateSignalPair>),
  ConditionalTransition,
}

impl Parse for StateSignalPairParser {
  fn parse(input: ParseStream) -> Result<Self> {
      if let Ok(_) = input.parse::<Token![?]>() {
        return Ok(Self::ConditionalTransition);
      }

      let from_state: StateOption = if input.lookahead1().peek(Token![_]) {
        input.parse::<Token![_]>()?;
        StateOption::AnyState
      } else {
        StateOption::SomeState(input.parse()?)
      };
      
      let on_ident_parse_res = input.parse::<Ident>();
      if on_ident_parse_res.is_err() {
        return Ok(Self::ChainEnd(from_state.into_option().unwrap()));
      }
      let on_ident = on_ident_parse_res.unwrap();
      if on_ident != "on" {
        panic!("on == {}, should be 'on'", on_ident);
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
      let mut signal: Ident;
      let mut pairs = Vec::new();
      let mut done = signals_set_parsed.is_empty();
      while !done {
        signal = signals_set_parsed.parse()?;

        signal_input_type =
          if signals_set_parsed.lookahead1().peek(token::Paren) {
            let signal_input_type_tokens;
            parenthesized!(signal_input_type_tokens in signals_set_parsed);
            Some(signal_input_type_tokens.parse()?)
          } else { None };

          pairs.push( 
            StateSignalPair { 
              from_state: from_state.clone().into_option(),
              signal: (signal, signal_input_type)
             }
          );   
          done = single_signal || signals_set_parsed.is_empty(); 
          if !done {
            signals_set_parsed.parse::<Token![|]>()?;
          }
        }
      Ok( match from_state {
        StateOption::SomeState(_) => Self::ChainJoint(pairs),
        StateOption::AnyState => Self::FromAnyStateChainStart(pairs),
      })
  }
}

fn quote_transition_handler(input: proc_macro::TokenStream, conditional: bool) -> proc_macro::TokenStream {
	let transition_parsed = parse_macro_input!(input as TransitionHandlerArgsParser);
  let fsm_ident = &transition_parsed.fsm_ident;
  let trait_ident = &trait_ident(fsm_ident);
  let any_state_ident = &Ident::new("_", Span::call_site());
  let state_ident = 
    match transition_parsed.state_signal_pair.from_state {
      Some(ref state) => state,
      None => any_state_ident,
  };
  let signal_ident = &transition_parsed.state_signal_pair.signal.0;
  let signal_input_type = &transition_parsed.state_signal_pair.signal.1;
  let body_block = &transition_parsed.body_item;
  let handler_ident = &callback_ident(state_ident, signal_ident);

  let tr_quoted = match signal_input_type {
    Some(input_type) => 
      if conditional {
        quote! {
          impl #fsm_ident {
            fn #handler_ident(input: &#input_type, data: &mut <Self as #trait_ident>::DataItem) -> <Self as #trait_ident>::StateItem
              #body_block
          }
        }
      } else {
        quote! {
          impl #fsm_ident {
            fn #handler_ident(input: &#input_type, data: &mut <Self as #trait_ident>::DataItem)
              #body_block
          }
        }
      }
  
    None => 
      if conditional {
        quote! {
          impl #fsm_ident {
            fn #handler_ident(data: &mut <Self as #trait_ident>::DataItem) -> <Self as #trait_ident>::StateItem
              #body_block
          }  
        }
      } else {
        quote! {
          impl #fsm_ident {
            fn #handler_ident(data: &mut <Self as #trait_ident>::DataItem)
              #body_block
          }  
        }      
      }
 
  };
//  println!(" +++++++++++ {}", tr_quoted);
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
//  let transitions = &parser.transition_tokens;
//  let any_state_transitions = &parser.any_state_transition_tokens;
//  let signals = &parser.signal_enum_tokens;
  let signal_enum_ident = &parser.signal_enum_ident;
  let state_enum_ident = &parser.state_enum_ident;
  let match_tr_entries = &parser.match_transition_tokens;
  let iter_item_ident = ChainIterItem::name_from_fsm(&fsm_ident);

  let quoted 
    = match data_type {
      Some(data_type) => quote! {
        trait #trait_ident {
          type StateItem: PartialEq + Clone + Copy;
          type SignalItem: PartialEq;
          type DataItem;
          #[cfg(feature = "meta_iter")]
          type IterItem;

          fn signal(&mut self, signal: &Self::SignalItem);
          fn data(&self) -> &Self::DataItem;
          fn state(&self) -> &Self::StateItem;
        }

        pub struct #fsm_ident {
          state: #state_enum_ident,
          data: #data_type,
        }

        impl #trait_ident for #fsm_ident {
          type StateItem = #state_enum_ident;
          type SignalItem = #signal_enum_ident;
          type DataItem = #data_type;
          #[cfg(feature = "meta_iter")]
          type IterItem = #iter_item_ident;

          fn signal(&mut self, signal: &Self::SignalItem) {
            self.state = match (self.state, signal) {
              #(#match_tr_entries),*,
              _ => self.state
            }
          }
          fn data(&self) -> &Self::DataItem {
            &self.data
          }
          fn state(&self) -> &Self::StateItem {
            &self.state
          }
        }
    
        impl #fsm_ident {
          pub fn new(state: #state_enum_ident, data: #data_type) -> Self {
            Self { 
              state, 
              data,
             }
          }
        }
    
      },
      None => 
        quote! {
          trait #trait_ident {
            type StateItem: PartialEq + Clone + Copy;
            type SignalItem: PartialEq;
            type DataItem;
            #[cfg(feature = "meta_iter")]
            type IterItem;
  
            fn signal(&mut self, signal: &Self::SignalItem);
            fn state(&self) -> &Self::StateItem;
          }
  
          pub struct #fsm_ident {
            state: #state_enum_ident,
          }
      
          impl #fsm_ident {
            pub fn new(state: #state_enum_ident) -> Self {
              Self { 
                state,
              }
            }
          }
  
          impl #trait_ident for #fsm_ident {
            type StateItem = #state_enum_ident;
            type SignalItem = #signal_enum_ident;
            type DataItem = ();
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
          }
      
        },  
  };

  let output = TokenStream::from(quoted.into_token_stream());

//  println!("output: {}", output.to_string());
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
 // let iter_item_ident = Ident::new( &format!("{}{}", fsm_ident, "IterItem"), Span::call_site() );
  //let state_enum_option_ident = Ident::new( &format!("Option<{}>", fsm_parsed.state_enum_ident), Span::call_site() )
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
  // extend AnyState to SomeState collection
  while let Some(index) = match_tr_entries.iter()
    .position(|item| item.0.as_option().is_none()) {
      let entry = match_tr_entries.swap_remove(index);

      match_tr_entries.extend(
        fsm_parsed.state_enum_tokens.iter()
          .map(|from| {
            let mut entry = entry.clone();
            entry.0 = StateOption::SomeState(from.clone());
            entry
          })
      );
  }

  while let Some(mut entry) = match_tr_entries.pop() {
    let mut chain = Vec::new();
    let mut to_state = &entry.3;

    while let Some(index) = match_tr_entries.iter()
      .position(|item| item.0.as_option() == to_state.as_ref()) {

      chain.push( ChainIterItem(fsm_ident.clone(), entry.0.into_option().unwrap(), entry.1.clone(), 
        entry.3.clone() ));
      entry = match_tr_entries.swap_remove(index);

      to_state = &entry.3;
    }
    chain.push( ChainIterItem(fsm_ident.clone(), entry.0.into_option().unwrap(), entry.1, entry.3.clone()));

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
    pub struct #iter_item_decl;

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
  
/*    impl core::fmt::Display for #iter_item_name {
      fn fmt(&self, f: &mut core::fmt::Formatter) -> core::fmt::Result {
        match &self.to {
          Some(thing) => write!(f, "({} on {} => {})", self.from, self.on, thing),
          None => write!(f, "({} on {} => ?)", self.from, self.on),
        }
      }
    }
*/  
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
    
  println!("------------{}", quoted);

  let output = TokenStream::from(quoted.into_token_stream());

return output;

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

