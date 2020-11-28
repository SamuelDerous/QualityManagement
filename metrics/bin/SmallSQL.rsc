module SmallSQL

import IO;
import List;
import ListRelation;
import Relation;
import String;
import Map;
import Set;
import util::Resources;
import util::Math;
import analysis::m3::Core;
import lang::java::m3::AST;
import lang::java::jdt::m3::Core;

/* code vanuit de cursus
*/
public list[str] printMethods(loc project) {
	M3 model = createM3FromEclipseProject(project);
	list[str] comparation = [];
	int count = 0;
	str compareLine;
	for (loc l <- methods(model)) {
		for(str s <- readFileLines(l)) {
		//str s = readFile(l);
			comparation += trim(s);
			//count += telIterations(s);
			println("=== <l> ===\n<s>");
		}
	}
	//print(count);
	return comparation;
	
}

public list[str] linesToCompare(set[loc] file) {
	list[str] lines = [];
	for(t <- readFileLines(file)) {
		if(!(/((\s|\/*)(\/\*|\s\*)|[^\w,\;]\s\/*\/)|(\/\/.)/ := t) && !(/((\n)$)|(^(\n))|^\s*$/ := t)) {
			if(!(startsWith(trim(t), "import")) && !(startsWith(trim(t), "package")) && !(startsWith(trim(t), "@")) &&
			!(startsWith(trim(t), "{")) && !(startsWith(trim(t), "}")) && !(startsWith(trim(t), "try")) &&
			!(startsWith(trim(t), "break")) && !(startsWith(trim(t), "continue")) && !(startsWith(trim(t), "return"))) {
				//println(t);
				lines += t;
			}
		}
	}
	return lines;
}

public int duplication(loc project) {
	int duplicationLines = 0;
	int amountOfLines = 6;
	//for(file <- files) {
		list[str] lines = printMethods(project);;
		str line = take(1, lines)[0];
		println(size(lines));
		//lines = drop(1, lines);
		//println(line);
		//println(linesToCompare[0]);
		int currentLine = 0;
		int i = 0;
		int j = 0;
		int t = 0;
		map[list[str], int] count = ( );
		while(i < size(lines) - 1) {
			list[str] comparation = [];
			list[str] toCompare = [];
			if(i + amountOfLines > size(lines) - 1) {
				comparation = slice(lines, i, (size(lines)) - i);
			} else {
				comparation = slice(lines, i, amountOfLines);
			}
			if(comparation in count) {
				count[comparation] += 1;
			} else {
				count += (comparation : 1);
			}
			println("=============test met i = <i>===================");
			for(int k <- [0 .. size(comparation)]) {
				println(comparation[k]);
			}
			println("\n\n");
			
			i += 1;
			j = 0;
			t = 0;
		}
	for(int clf <- range(count)) {
		if(clf > 1) {
			
			duplicationLines += clf;
		}
	}
	return duplicationLines;
}

/* krijg alle bestanden in het bestand (eindigend op .java)
   @return de bestanden in een set
*/
public set[loc] model1(loc project) {
	Resource smallSql = getProject(project);
	return {l | /file(l) <- smallSql, l.extension == "java"}; 
}

/* method to count the amount of units in the project
   according to the text a unit is the smallest part of code that
   can be executed and for java or C# that is a method.
   @param de bestanden die bekeken moeten worden
   @return aantal methodes
*/

public int countUnits(set[loc] bestanden) {
	set[Declaration] decls = createAstsFromFiles(bestanden, false);
	int n = 0;
	visit (decls) {
		case \method(_, _, _, _, _): n += 1;
		case \constructor(_, _, _, _): n += 1;	
	}
	return n;
}


public bool aflopend(tuple[&a, num] x, tuple[&a, num] y) {
   return x[1] > y[1];
}

/* methode om het aantal regels te tellen die leeg zijn of bestaan 
   uit commentaar (//, /*, *)
   @param de bestanden die bekeken moeten worden
   @return aantal lege of commentaarregels
*/

public int countCommentsOrBlankLines(set[loc] bestanden) {
	n = 0;
	for(s <- bestanden) {
		for(t <- readFileLines(s)) {
			if(/((\s|\/*)(\/\*|\s\*)|[^\w,\;]\s\/*\/)|(\/\/.)/ := t || /((\n)$)|(^(\n))|^\s*$/ := t) {
				n += 1;
			}
		}
	}
	return n;

}

public lrel[str, Statement] methodenAST(loc project) {
set[loc] bestanden = model1(project);
set[Declaration] decls = createAstsFromFiles(bestanden, false);
lrel[str, Statement] result = [];
visit (decls) {
case \method(_, name, _, _, impl): result += <name, impl>;
case \constructor(name, _, _, impl): result += <name, impl>;
}
return(result);
}


public int telIterations(Statement d) {
   
   int count = 0;
   visit(d) {
   	  case \if(_,_): count += 1;
      case \if(_,_,_): count += 1;
      case infix(_,"&&",_): count += 1;
      case infix(_, "||",_): count += 1;
      case \case(_): count += 1;
      case \conditional(_,_,_): count += 1;
   } 
   return count;
}

public int telLoops(Statement d) {
	int count = 0;
	visit(d) {
		case \do(_,_): count += 1;
		case \foreach(_,_,_): count += 1;
		case \for(_,_,_,_): count += 1;
		case \for(_,_,_): count += 1;
		case \while(_,_): count += 1;
	}
	return count;
}

public int telExceptions(Statement d) {
	int count = 0;
	visit(d) {
		case \catch(_,_): count += 1;
		case \throw(_): count += 1;
	}
	return count;
}

public str volumeScore(int loct) {
	int kloc = loct / 1000;
	if(kloc < 66) {
		return "++";
	} else if (kloc < 246) {
		return "+";
	} else if (kloc < 665) {
		return "o";
	} else if (kloc < 1310) {
		return "-";
	} else if (kloc >= 1310) {
		return "--";
	}
	return "error";
}

public str complexityScore(real moderate, real high, real veryHigh) {
	if(moderate <= 30.0 && high <= 0.0 && veryHigh <= 0.0) {
		return "++";
	} else if (moderate <= 30.0 && high <= 5.0 && veryHigh <= 0) {
		return "+";
	} else if(moderate <= 40.0 && high <= 10.0 && veryHigh <= 0.0) {
		return "o";
	} else if (moderate <= 50.0 && high <= 15.0 && veryHigh <= 5.0) {
		return "-";
	} else {
		return "--";
	}
}

public str duplicationScore(real duplication) {
	if(duplication < 3.0) {
		return "++";
	} else if (duplication < 5.0) {
		return "+";
	} else if (duplication < 10.0) {
		return "o";
	} else if (duplication < 20) {
		return "-";
	} else {
		return "--";
	}
}

public str testcoverage(real percCoverage) {
	if(percCoverage < 20.0) {
		return "--";
	} else if (percCoverage < 60.0) {
		return "-";
	} else if (percCoverage < 80.0) {
		return "o";
	} else if (persCoverage < 95.0) {
		return "+";
	} else {
		return "++";
	}
} 


public void metrics() {
	loc project = |project://testProject|;
	set[loc] bestanden = model1(project);
	M3 model = createM3FromEclipseProject(project);
	//loc bestand = |project://smallsql/src/smallsql/database/ExpressionFunctionIIF.java|;
	//println(model.modifiers[bestand]);
	
	methodenList = {b | <a,b> <- model.containment, a.scheme == "java+class", b.scheme=="java+method" || b.scheme=="java+constructor"};
	//println(methodenList);
	int blankLinesInUnit = countCommentsOrBlankLines(methodenList);
	real totaalAantalLinesInUnits = 0.0;
	stats = methodenAST(project);
	real difficulties = 0.0;
	/*for(Statement i <- stats) {
		int difficulty = telIterations(i); // + telLoops(i) + telExceptions(i);
		println(difficulty);
		difficulties += difficulty;	
	}*/
	//int gemDif = difficulties / size(stats);
	//println("<difficulties> <size(stats)> <gemDif>\n\n");
	//println(difficulties);
	difficulty = [telIterations(s) + telLoops(s) + telExceptions(s) | <name, s> <- stats];
	for(int i <- difficulty) {
		difficulties += i;
	}
	complexity = difficulties / size(stats);
	for(k <- methodenList) {
		//println("<k>: <size(readFileLines(k))>");
		totaalAantalLinesInUnits += size(readFileLines(k));
	}
	totaalAantalLinesInUnits -= blankLinesInUnit;
	int duplicationLines = duplication(project);
	//print(methodenList);
//telMethoden = { <a, size(methoden[a])> | a <- domain(methoden) };
/*for (<a,n> <- methoden)
println("<a>: <n> methoden");
*/
	int commentsOrBlankLines = countCommentsOrBlankLines(bestanden);
	int locs = 0;
	map[loc, int] regels = (l:size(readFileLines(l)) | l <- bestanden );
   	for (<l, b> <- toList(regels)) {
      locs += b;
    }
    locs = locs - commentsOrBlankLines;
    println("lines of code: <locs>");
    println("Number of units: <size(methodenList)>");
    println("average unit size: <precision(totaalAantalLinesInUnits / size(methodenList), 5)>");
    println("average unit complexity: <precision(complexity, 5)>");
    println("duplication: <duplicationLines>\n");
    println("Volume score: ");
    println("Unit size score:");
    println("Unit complexity score:");
    println("Duplication score:\n");
    println("analysability score:");
    println("changability score:");
    println("testability score:\n");
    println("Overall maintainability score:");
    
    
}



