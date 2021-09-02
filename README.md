 # Finite State Machine
 Finite state machine can be considered a transformation from 2D space of {S, E} to {S}
 where S and E are sets associated with States and Events respectively.
 Rust provides syntax that covers this pattern:
 ```rust,ignore
   let next_state =
     match (state, event) {
       (StateA, Event1) => StateB,
       // and generally on:
       //(State#i, Event#j) => State#k,
       (_, _) => SomeVariant
     };
 ```
 From a programmer's perspetive an FSM could be seen as a black box which reacts on Events from
 the outer, from the machine's perspective, world, depending on its actual State.
 These "reactions" or transitions are what is expected to be programmed once the machine template is defined.
 This crate presents procedural macros as a trial to provide some sugar to this pattern.
 As there is no dynamic data manipulation involved except user defined state context, each transition is supposed to be as fast as two method calls.
 To use it include this in your code:
 ```rust,ignore
 #[macro_use]
 extern crate fsm;
 ```
 The main macro that defines the machine's type looks like so:
 ```rust,ignore
 fsm!( UselessMachine [
   StateA on Signal1 => StateB,
   StateB on Signal2 => StateC,
   StateB on Signal3 => StateC,
   StateC on Signal2 => StateA,
   Idle on Start => StateA,
   _ on Reset => Idle,
 ]);
 ```
 which is equivalent to more compact chained notation:
 ```rust,ignore
 fsm!( UselessMachine [
   StateA on Signal1 => StateB on (Signal2 | Signal3) => StateC on Signal2 => StateA,
   _ on Reset => Idle on Start => StateA
 ]);
 ```
 From this declaration the macro will deduce the following:
 ```rust,ignore
   pub enum UselessMachineStates {
     StateA,
     StateB,
     StateC,
     Idle,
   }
 
   pub enum UselessMachineSignals {
     Start,
     Reset,
     Signal1,
     Signal2,
     Signal3,
   }
   
   pub struct UselessMachine {
     ...
   }
 ```
 I called this machine Useless for a reason: it receives scarse information from the outer world and
 is unable to produce coherent reactions because no user data is associated with its state.
 The only way to obtain something useful from such a machine is by repeating matching its state.
 
 Here is how a machine definition can be extended:
 ```rust,ignore
   // user data associated with state
  struct Count {
   a_count: usize,
   b_count: usize,
   other_count: usize,
 }
 // this will count letters only, discriminating A & B from the rest
 // the rest of the states is introduced just for presentation purpose
 fsm!( LetterCounter<Count> [
   Idle on Start => Started,
   _ on LetterA => IncA on Other(char) => OtherAfterA,
   _ on LetterB => IncB,
   _ on Other => IncOther,
   _ on (Number(u32) | Float(f64)) => NumberSt,
   _ on Reset => Idle,
 ]);
 ```
 A struct LetterCounter with associated type Count is generated.
 Every individual signal can carry input typed with type in parentheses.
 (note the detail here: once Other(char) is declared, there is no need to repeat (char) in
 declaration - will panic on type clash).
 Now, this is not going to compile as we lack the essence - transitions, so here the second
 part of our declaration comes - define a method for every arrow:
 ```rust,ignore
 // this reads: do sth when Start signal received while in Idle state
 transition_handler!( Idle on Start for LetterCounter {
 });
 // this reads: do sth when LetterA signal received no matter in which actual state
 from_any_state_transition_handler!(LetterA for LetterCounter {
   data.a_count += 1;
 });
 from_any_state_transition_handler!(LetterB for LetterCounter {
   data.b_count += 1;
 });
 from_any_state_transition_handler!(Other(char) for LetterCounter {
   data.other_count += 1;
   println!("Unrecognized counted: {}", input);
 });
 transition_handler!(IncA on Other(char) for LetterCounter {
   data.other_count += 1;
   println!("Unrecognized counted: {}", input);
 });
 from_any_state_transition_handler!(Reset for LetterCounter {
   data.a_count = 0;
   data.b_count = 0;
   data.other_count = 0;
 });
 from_any_state_transition_handler!(Number(u32) for LetterCounter {
   // do sth with Numbers
 });
 from_any_state_transition_handler!(Float(f64) for LetterCounter {
   // do sth with Floats
 });
```

 These macros hide two references: a mutable one to data associated with state exposed by 'data',
 and another immutable 'input' delivered with the signal.
 
 As LetterCounter is a struct, you can expand its API if you want to:
 ```rust,ignore
 impl LetterCounter {
   pub fn start(&mut self) {
     self.signal(&Start);
   }
 }
 ```
 LetterCounter::signal(...) method encapsulates the transition matcher.
 ```rust,ignore
 from_any_state_transition_handler!(Signal for Machine { // ... 
 });
 ``` 
 is alternative for equivalent notation:
 ```rust,ignore
 transition_handler!(_ on Signal for Machine { // ... 
 });
 ``` 
 
 Now define the instance:
 ```rust,ignore
 let mut counter = LetterCounter::new(Idle, Count { a_count: 0, b_count: 0, other_count: 0 });
 ```
 And use it:
 ```rust,ignore
 counter.start();
 counter.signal(&LetterA);
 counter.signal(&Other('x'));
 counter.signal(&LetterA);
 counter.signal(&LetterB);
 counter.signal(&Number(8));
 counter.signal(&LetterB);
 counter.signal(&Other('x'));

 let n = counter.data();
 println!("counted: a -> {}, b -> {}, others -> {}", n.a_count, n.b_count, n.other_count);
 ```
 One can notice that in this example no code directly refers to current fsm's state 
 (although it can be accessed via state() method).
 
 I consider current state an implementation detail of machine's black box which does not
 provide sufficient information about past, namely it does not make much sense to know what 
 current state is out of context of some transition.  
 
 There is another way to break the black box though.
 Consider that this silly counter needs to distinguish the situation of more than 5 B letters counted
 entering a specific state, call it MoreThan5B.
 
 One could define it this way:
 ```rust,ignore
 Started on LetterB => IncB_1 on LetterB => IncB_2 on LetterB... and so forth.
 ```
 They call it transition explosion.
 
 There is an alternative fork pattern for this scenario :
 ```rust,ignore
  fsm!( LetterCounter<Count> [
     Idle on Start => Started,
     _ on LetterA => IncA on Other(char) => OtherAfterA,
     _ on LetterB => ?, // <-------- 
     _ on Other => IncOther,
     _ on Reset => Idle,
 ]);
 ```
 This interrogation sign declares that the LetterCounter delegates the determination of resulting
 state to the transition handler itself.
 And here is where this macro jumps out:
 ```rust,ignore
 conditional_handler!(_ on LetterB for LetterCounter {  
   data.b_count += 1;

   if data.b_count < 5 {
     IncB
   } else {
     MoreThan5B
   }
 });
 ```
 Now, this won't compile, the machine doesn't know what IncB and MoreThan5B are, so let's add some
 silly transitions to our machine:
 ```rust,ignore
  fsm!( LetterCounter<Count> [
     Idle on Start => Started on LetterB => IncB, // <-- here
     _ on LetterA => IncA on Other(char) => OtherAfterA,
      // and here
      MoreThan5B on LetterB => MoreThan5B,
     _ on LetterB => ?,
     _ on Other => IncOther,
     _ on Reset => Idle,
 ]);
 ```
 and their corresponding handlers:
 ```rust,ignore
 transition_handler!( Started on LetterB for LetterCounter {
   data.b_count += 1;
 });
 transition_handler!( MoreThan5B on LetterB for LetterCounter {
  data.b_count += 1;
  println!("On MoreThan5B");
 });
 ```
 This design defines a relaxed machine in sense that it won't change state on signal
 no transition for which exists for current state.

 ## Moore State Machine
 It's often useful to define an action to be performed upon state entry and/or exit regardless
 of a transition leading to the change.
 This can be used in common scenarios of initialization, for instance, and can save some code 
 repetition.
 Below is how the machine's declaration syntax is extended to cover such a case:
 ```rust,ignore
 // using the previous example, take the reset code out of Transition handler to Idle State Entry handler
 fsm!( LetterCounter<Count> [
   Idle on Start => Started,
   _ on LetterA => IncA on Other(char) => OtherAfterA,
   _ on LetterB => IncB,
   _ on Other => IncOther,
   _ on (Number(u32) | Float(f64)) => NumberSt,
   _ on Reset => Idle,
   ],
   [Idle entry, Start exit]
 );
 on_state_handler!( Idle entry for LetterCounter {
   data.a_count = 0;
   data.b_count = 0;
   data.other_count = 0;
});
 on_state_handler!( Start exit for LetterCounter {
 // do sth here
});
 ```
 This syntax recognizes two words only: 'entry' and 'exit'.
 
 # Pushdown Automaton
 introduces a third variable to the equation which is a stack which, combined with a state and 
 input signal presents a model of taking transitions considerably more powerful than a regular state machine.
 It is capable of parsing nested patterns, for example. 
 Note that according to formal definition signal and stack symbol alphabets do not necesarily coincide.

 In this crate the stack is implemented as a standard Vec with no encapsulation while the formal definition
 for PDA stack can be more restrictive as for permitted stack operations.
 So here is the declaration example:
 
 
 ```rust,ignore
     fsm!( LittleParser<ParserCtx, StackCtx> [ // ...
 // state context ---------^          ^---------------- stack context (impls PartialEq) 
     // ...
     ]);
 ```
 Once declared so, the 'stack' mutable reference becomes accessible in transition handlers.
 This stack can be polled, pushed and however manipulated to determine conditional forks on
 state transitions.
 
 As an experiment I introduced an extended syntax for transition signatures in order to pursuit
 for deterministic automaton for some common patterns which for the moment are:
 
 'cmp_pop expr' - stands for compare the stack's top with the given expression and if true, pop it;

 'cmp_pop_if_last expr' - the same as above but applies only when the stack contains only one item;

 'peek_cmp expr' - compare the stack's top element with the given expression without modifying the stack;

 'pop' - pop from the stack unconditionally upon transition;

 'empty' - condition transition with stack emptiness;

 '!empty' - the negation of the above;
 
  Using this syntax one can introduce a palette of determenistic transitions under more complex conditions
  which are encoded directly in transition signature rather than in the code.

  For example:
 
 ```rust,ignore
     fsm!( LittleParser<ParserCtx, StackCtx> [ 
         // code omitted ...
         // TextSegment is a State, RightBracket is a current symbol delivered with a Signal
         // and (Left)Bracket is a symbol that can possibly be on top of the Stack...
         // if so recognize it as a valid pattern and transtion to the same State 
         // then stack popping can be performed in the handler    
         TextSegment on RightBracket peek_cmp Bracket 
         // next possible situation is that we have the same State and Signal, but the Stack contains
         // other symbol so treat this as an unbalanced segment
         => TextSegment on RightBracket => InvalidSegment, 
         // more code omitted ...
   ]);
 ```
  So we have here two distinct deterministic transitions instead of a conditional fork:
 ```rust,ignore
 transition_handler!(TextSegment on RightBracket peek_cmp Bracket for LittleParser {
 // ...
 });
 transition_handler!(TextSegment on RightBracket for LittleParser {
 // ...
 });
 ```
  
 The internal matching for is ordered in a way that more specific 
  patterns are preferred over the more common ones so in the above example the first condition is checked
  first regardless of its visual location in the machine's declaration (at least this was my intention).
  
 ## meta_iter Feature
 
 The crate defines a feature "meta_iter" which, when is on brings a machine's iterator into scope.
 Note that there is no dynamic collection to iterate on, this iterator operates on metadata
 resulting from waste product of declarations of machine's enums.
 This feature brings a bit of text to the code and is only useful for enumerating transitions
 while debugging, for instance.
 The result could be then sent to a graph visualization software or just printed out.
 
 For now comprehensive output can be obtained for an FSM only, a PDA will yield the same
 output as if it was an FSM.
  
 It works like so:
 ```rust,ignore
 let mut chains = LetterCounter::chains();
 while let Some(mut chain) = chains.next() {
  while let Some(item) = chain.next() {
    let s = if let Some(to) = item.to {
        format!("{} -> {} by {}\n", item.from, to, item.on)
      } else {
        format!("{} -> {} by {}\n", item.from, "ConditionalMultichoice", item.on)   
      };
      println!("{}", s);
  }
}
```
 The result of printout will be a list machine's transitions. Note that there is almost no chance
 that the list printout coincide with yours machine layout view in source code.
 
 ## fsm_gen_code Feature
 When on this feature generates a string containing the Rust text created by the macro.
 The string is in format of an fsm's name concatenated with _GEN_CODE identifier.
 For example for MyMachine the string is accessed by 
 
 ```rust,ignore
 MY_MACHINE_GEN_CODE 
 ```
 constant.
 
   
 ## Caveats
 
 Lifetime parsing for user data type is not covered, so this won't compile:
 ```rust,ignore
  fsm!( LetterCounter<WithLifetime<'a>> [...]);
 ```

