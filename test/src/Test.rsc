module Test

import IO;
import List;
import Map;
import Set;
import Relation;
import util::Resources;
import analysis::graphs::Graph;
import lang::java::jdt::m3::Core;
import lang::java::m3::AST;
import vis::Figure;
import vis::Render;
import vis::KeySym;


// copied from solution
public int telIfs(Statement d) {
	int count = 0;
	visit(d) {
		case \if(_,_): count=count+1;
		case \if(_,_,_): count=count+1;
	}
	return count;
}

// copied from solution
public bool aflopend(tuple[&a, num] x, tuple[&a, num] y) {
return x[1] > y[1];
}


// this is from the solution
public rel[int, int] delers(int getal) {
		return { <n, i> | int n <- [1 .. getal], int i <- [1 .. n+1], n % i == 0};	
}

// this is my own implementation
public list[set[int]] delersSet(int getal) {
	list[set[int]] testGetal;
	for(int i <- [1 .. getal + 1]) {
		set[int] op = ({n | int n <- [1 .. getal + 1], i % n == 0});
		if (i == 1) { // needed to instantiate the list;
			testGetal = [op];
	 	} else {
			testGetal += op; // if instantiated just add a new set
		}
	}
	return testGetal;
}

public list[int] maxDivisors(int getal) {
	list[set[int]] divisorsPerGetal = delersSet(getal);
	int max = 0;
	list[int] maxDivisors = [0];
	int sizeList = size(divisorsPerGetal);
	for(int i <- [0 .. sizeList]) {
		if(size(divisorsPerGetal[i]) > max) {
			max = size(divisorsPerGetal[i]);
			maxDivisors = [(i + 1)];
		} else if (size(divisorsPerGetal[i]) == max) {
			maxDivisors += i + 1;
		}
	}
	return maxDivisors;
}

public void primeNumbers(int getal) {
		list[set[int]] divisorsPerGetal = delersSet(getal);
		int sizeList = size(divisorsPerGetal);
		for(int i <- [0 .. sizeList]) {
			if(size(divisorsPerGetal[i]) <= 2) {
				println(i + 1);
			}
		}
}

 public Graph[str] component = {<"A", "B">, <"A", "D">, <"B", "D">, <"B","E">, <"C", "B">, <"C", "E">, <"C", "F">,
 		<"E", "D">, <"E", "F">};

// I had to peak to the solutions a lot for this one
public void exercise6() {
	println("Hello");
	list[str] eu=["Austria", "Belgium", "Bulgaria", "Czech Republic","Cyprus", "Denmark", "Estonia", "Finland", "France", "Germany","Greece", "Hungary", "Ireland", "Italy", "Latvia", "Lithuania","Luxembourg", "Malta", "The Netherlands", "Poland","Portugal", "Romania", "Slovenia", "Slovakia", "Spain","Sweden", "United Kingdom"];
	println("Oefening 6A");
	println({s | s <- eu, /s/i := s});
	println("Oefening 6B");
	println({s | s <- eu, /e.*e/i := s});
	println("Oefening 6C");
	println({s | s <- eu, /^([^e]*e){2}[^e]*$/i := s});
	println("Oefening 6D");
	//the name contains no n and also no e
	println({s | s <- eu, /^[^ne]*$/i := s});
	println("Oefening 6E");
	// the name contains any letter at least twice
	println({s | s <- eu, /<x:[a-z]>.*<x>/i := s});
	println("Oefening 6F");
	// change the first a in an o
	println({begin+"o"+end | a <- eu, /^<begin:[^a]*>a<end:.*>$/i := a});
	println("Oefening 7A");
	// Compute the relationship between the natural numbers up to 100 and their divisors.
	// Optionally make the upper limit a paramater
	println(delers(4));
}

public void exercise7() {
	// oefening 7a
	println(delers(100));
	// oefening 7b
	println(maxDevisors(100));
	// oefening 7c
	println(primenumbers(100));
}

public void exercise8() {
	// oefening 8a
	println(carrier(component));
	// Oefening 8b
	println(size(carrier(component)));
	// oefening 8c
	println(top(component));
	// oefening 8d
	println(successors(component, "A"));
	// oefening 8e
	println((carrier(component)) - (component*)["C"]);
	// oefening 8f
	println((comp:size(component[comp]) | comp <- carrier(component)));
}

// oefening 9a en 9b
public void exercises9A() {
	Resource jabber = getProject(|project://Jabberpoint-le3/|);
	int javaFiles = 0;
	rel[value, int] javaF = {};
	rel[int, value] javaFInt = {};
	visit(jabber) {
		case file(l):
			if (l.extension == "java") {
				javaFiles += 1; // exercise a
				int javalines = size(readFileLines(l)); 
				javaF += {<l,javalines>};
				javaFInt += {<javalines, l>};
			}
	}
	lrel[value, int] testRel = sort(javaF);
	lrel[int, value] testRelInt = sort(javaFInt);
	for(int i <- [0 .. size(testRel)]) {
		println(testRel[i]);
	}
	println();
	for(int i <- [0 .. size(testRelInt)]) {
		println(testRelInt[i]);
	}
	println("Total of java Files: <javaFiles>");
}

// oefening 9c en 9e
public void exercise9C() {
	Resource jabber = getProject(|project://Jabberpoint-le3/|);
	rel[int, value] methods = {};
	rel[str, value] methodNames = {};
	visit(jabber) {
		case file(l):
			if (l.extension == "java") {
				set[Declaration] asts = 
					createAstsFromFiles({l}, false);
				int numMethods = 0;
				int numIfs = 0;
				visit(asts) {
					case \method(_,name,_,_,impl): {
						numMethods += 1; 
						methodNames += {<name,impl>};
					}
					case \constructor(name,_,_,impl): {
						numMethods += 1;
						methodNames += {<name, impl>};
					}
				}
				methods += {<numMethods, l>};
			}
	}
	lrel[int, value] methodsSorted = sort(methods);
	for(int i <- [0 .. size(methodsSorted)]) {
		println(methodsSorted[i]);
	}
	aantalIfs = sort([ <name, telIfs(s)> | <name, s> <- methodNames ],
	aflopend);
	println(aantalIfs);
}

// oefening 9d
public void exercise9D() {
	loc project = |project://Jabberpoint-le3/|;
	M3 model = createM3FromEclipseProject(project);
	subklassen = invert(model.extends);
	telKinderen = { <a, size((subklassen+)[a])> | a <-
	domain(subklassen) };
	for (<a, n> <- sort(telKinderen, aflopend))
		println("<a>: <n> subklassen");
}	 				

// oefening 10a
public void exercises10() {
	list[Figure] figures = [];
	for(int i <- [0 .. 10]) {
		figures += box(size(40), fillColor("red"), resizable(false));
	}
	render(hcat(figures, gap(5)));
}

// oefening 10b
public void exercise10b() {
	s = "";
	s2 = "";
	b = box(size(40), fillColor("red"), resizable(false), 
		onMouseDown(bool (int butnr, map[KeyModifier,bool] modifiers) {
			render(b2);
			return true;
		}));
	
	b2 = ellipse(size(40), fillColor("green"), resizable(false),
		onMouseDown(bool (int butnr, map[KeyModifier,bool] modifiers) {
			render(b);
			return true;
		}));
	render(b);
}

oefening 10c
public void exercise10c() {
	map[str, int] jabberSizes =
		("AboutBox.java":28, "Accessor":30, "BitmapItem":67,
		"DemoPresentation":50, "JabberPoint":37, "KeyController":44,
		"MenuController":109, "Presentation":107, "Slide":85,
		"SlideItem": 38, "SlideViewerComponent":62,
		"SlideViewerFrame":36, "Style.java":57, "TextItem.java":108,
		"XMLAccessor":112);
	t = treemap([box(text(filename),area(no), fillColor(arbColor())) | <filename,no> <-
		toRel(jabberSizes) ]);
	render(t);
}

// this is not needed; probably a test
public void exercises9C() {
	set[Declaration] asts = 
		createAstsFromFiles({|project://Jabberpoint-le3/src/XMLAccessor.java|}, false);
	int numLoops = 0;
	
	visit(asts) {
		case \for(_,_,_): numLoops=numLoops+1;
		case \for(_,_,_,_): numLoops=numLoops+1;
		case \foreach(_,_,_): numLoops=numLoops+1;
	}
	println("<numLoops> for loops");
}



