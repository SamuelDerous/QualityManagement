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

public void exercise9C() {
	Resource jabber = getProject(|project://Jabberpoint-le3/|);
	rel[int, value] methods = {};
	rel[int, value] ifs = {};
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
					//case \if(_,_): numIfs += 1;
					//case \if(_,_,_): numIfs += 1;
				}
				methods += {<numMethods, l>};
				//ifs += {<numIfs, l>};
			}
	}
	//println(methods);
	lrel[int, value] methodsSorted = sort(methods);
	
	for(int i <- [0 .. size(methodsSorted)]) {
		println(methodsSorted[i]);
	}
	aantalIfs = sort([ <name, telIfs(s)> | <name, s> <- methodNames ],
	aflopend);
	println(aantalIfs);
}

public void exercises10() {
	list[Figure] figures = [];
	for(int i <- [0 .. 10]) {
		figures += box(size(40), fillColor("red"), resizable(false));
	}
	render(hcat(figures, gap(5)));
}

public void exercise10b() {
	/*b0 = box(size(40), fillColor("red"), resizable(false),
	onMouseDown(bool (int nummer, map[KeyModifier,bool] modifiers) {
		b0 = box(size(40), fillColor("green"), resizable(false));
		return true;
		}));
	render(b0);*/
	s = "";
s2 = "";
b = box(size(40), fillColor("red"), resizable(false), 
	onMouseDown(bool (int butnr, map[KeyModifier,bool] modifiers) {
		render(b2);
		return true;
	}));
	
b2 = ellipse(size(40), fillColor("green"), resizable(false),
		onMouseDown(bool (int butnr, map[KeyModifier,bool] modifiers) {
		//b2 = b1;
		render(b);
		return true;
	}));
render(b);
}

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

public int telIfs(Statement d) {
	int count = 0;
	visit(d) {
		case \if(_,_): count=count+1;
		case \if(_,_,_): count=count+1;
	}
	return count;
}


public bool aflopend(tuple[&a, num] x, tuple[&a, num] y) {
return x[1] > y[1];
}

public void exercise9D() {
	loc project = |project://Jabberpoint-le3/|;
	Resource jabber = getProject(|project://Jabberpoint-le3/|);
	set[loc] bestanden = { l | /file(l) <- jabber, l.extension == "java"};
	M3 model = createM3FromEclipseProject(project);
	subklassen = invert(model.extends);
	telKinderen = { <a, size((subklassen+)[a])> | a <-
	domain(subklassen) };
	for (<a, n> <- sort(telKinderen, aflopend))
		println("<a>: <n> subklassen");
}	 				

public void exercises9B() {
	M3 model = createM3FromEclipseProject(|project://Jabberpoint-le3/|);
	for(<a,b> <- model.extends) {
		println("<a> extends <b>");
	}
}

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

public rel[int, int] delers(int getal) {
		return { <n, i> | int n <- [1 .. getal], int i <- [1 .. n+1], n % i == 0};	
}

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
		//println("<i> : <size(divisorsPerGetal[i])>: <divisorsPerGetal[i]>");
		if(size(divisorsPerGetal[i]) > max) {
			max = size(divisorsPerGetal[i]);
			maxDivisors = [(i + 1)];
		} else if (size(divisorsPerGetal[i]) == max) {
			maxDivisors += i + 1;
		}
	}
	return maxDivisors;
	
}

public void primeNumbers() {
		list[set[int]] divisorsPerGetal = delersSet(100);
		int sizeList = size(divisorsPerGetal);
		for(int i <- [0 .. sizeList]) {
			if(size(divisorsPerGetal[i]) <= 2) {
				println(i + 1);
			}
		}
}

 public Graph[str] component = {<"A", "B">, <"A", "D">, <"B", "D">, <"B","E">, <"C", "B">, <"C", "E">, <"C", "F">,
 		<"E", "D">, <"E", "F">};

public void exercises8() {
	println(carrier(component));
	println("8A");
	println(size(carrier(component)));
	println(size(component));
	println(top(component));
	println(successors(component, "A"));
	println((carrier(component)) - (component*)["C"]);
	println((comp:size(component[comp]) | comp <- carrier(component)));
}

public void exercise5() {
	println("Hello");
	list[str] eu=["Austria", "Belgium", "Bulgaria", "Czech Republic","Cyprus", "Denmark", "Estonia", "Finland", "France", "Germany","Greece", "Hungary", "Ireland", "Italy", "Latvia", "Lithuania","Luxembourg", "Malta", "The Netherlands", "Poland","Portugal", "Romania", "Slovenia", "Slovakia", "Spain","Sweden", "United Kingdom"];
	//println(eu);
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

