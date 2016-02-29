Semant/Main.class : Semant/Main.java
	javac -g */*.java

clean :
	rm */*.class

parse : Parse/Main.class
	java Parse.Main test.tig

Parse/Main.class : Parse/Main.java
	javac -g */*.java
