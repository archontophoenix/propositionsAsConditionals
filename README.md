Inspired by a discussion the other day with Chris Clark.

It is often the case in dependently typed languages that you implement an idea
in two different forms: as an inductive type, and as a function, where the
inductive type represents a proposition and the function a decision procedure
for the proposition. For example, you might have a proposition that one natural
number m is less than or equal to another number n (the Idris standard library's
LTE m n), but also have a Boolean function that tests for the same condition
(Idris's lte m n). Chris and I agree that it is annoying to use two different
names for what is essentially the same concept.

I was inspired to wonder whether Idris's typeclasses were sufficiently powerful
to let you use the proposition in a way that looks like the condition in an
if-then-else (you use the typeclass to map the proposition to its decision
procedure). And it works!

Now, is it possible to imagine a language where you write just the decision
procedure, and the language derives the proposition automatically (or even
vice versa)?
