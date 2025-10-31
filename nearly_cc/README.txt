The only feature I did not implement was using different names for parameters between the function declaration and definition.
There is nothing particularly signifigant here, except there are some hacky work arounds for field references, mostly in the 
form of booleans in nodes which are set to know if the underlying type of the ref is an array. 
Most of this implementation revolves round the idea of setting the symbol for each node. This is particularly important when resolving operations, and allows the reuse of functions since everything by default is expecting their children to have their nodes set.
I am leaving in most of the TODO comments, because I have to reuse this code for AS3.