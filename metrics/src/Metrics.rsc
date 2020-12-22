module Metrics

import IO;
import List;
import ListRelation;
import String;
import Map;
import Set;
import util::Math;
import analysis::m3::Core;
import lang::java::m3::AST;
import lang::java::jdt::m3::Core;

import extraction::Extraction;
import extraction::TestabilityReport;
import computation::Complexity;
import computation::Duplication;
import computation::Overall;
import computation::Testing;
import computation::Volume;

public void metrics() {
	loc project = |project://smallsql|;
	set[loc] bestanden = model1(project);
	set[loc] testBestanden = testModel(project);
	M3 model = createM3FromEclipseProject(project);
	methodenList = {b | <a,b> <- model.containment, a.scheme == "java+class", b.scheme=="java+method" || b.scheme=="java+constructor"};
	int blankLinesInUnit = countCommentsOrBlankLines(methodenList);
	real totaalAantalLinesInUnits = 0.0;
	stats = getMethods(project);
	real difficulties = 0.0;
	difficulty = [telIterations(s) + telLoops(s) | <name, s> <- stats];
	asserts = countAsserts(testBestanden);
	for(int i <- difficulty) {
		difficulties += i;
	}
	if(difficulties > 1) {
		difficulties += 1;
	}
	
	complexity = difficulties / size(stats);
	for(k <- methodenList) {
		totaalAantalLinesInUnits += size(readFileLines(k));
	}
	totaalAantalLinesInUnits -= blankLinesInUnit;
	real duplicationLines = duplication(project);
	//println(difficulty);
	int commentsOrBlankLines = countCommentsOrBlankLines(bestanden);
	int locs = 0;
	map[loc, int] regels = (l:size(readFileLines(l)) | l <- bestanden );
   	for (<l, b> <- toList(regels)) {
      locs += b;
    }
    
    tuple[real moderate, real complex, real difficult] amounts = computeComplexityPerUnit(project);
    str compl = complexityScore(amounts.moderate, amounts.complex, amounts.difficult);
    tuple[real moderate, real complex, real difficult] sizePerUnit = computeUnitSize(project);
    str unitSize = complexityScore(sizePerUnit.moderate, sizePerUnit.complex, sizePerUnit.difficult);
    real testPerc = testReport();
    str testCoverage = testcoverage(testPerc);
    locs = locs - commentsOrBlankLines;
    str volScore = volumeScore(locs);
    str dupScore = duplicationScore(duplicationLines);
    str testScore = testability (compl, unitSize, testCoverage);
    str analyseScore = analysability(volScore, dupScore, unitSize, testScore);
    str changeScore = changeability(compl, dupScore);
    str maintainScore = "--"; //analysability(analyseScore, changeScore, testScore);
    
    println("lines of code: <locs>");
    println("Number of units: <size(methodenList)>");
    println("average unit size: <precision(totaalAantalLinesInUnits / size(methodenList), 5)>");
    println("average unit complexity: <precision(complexity, 5)>");
    println("duplication: <precision(duplicationLines, 4)>%\n");
    println("Testcoverage: <precision(testPerc, 5)> %");
    println("Amount of asserts: <asserts>");
    println("Assert Density: <precision(computeAssertDensity(asserts, countTestLines(project)), 5)>%\n");
    println("Volume score: <volScore>");
    println("Unit size score: <unitSize>");
    println("Unit complexity score: <compl>");
    println("Duplication score: <dupScore>\n");
    println("analysability score: <analyseScore>");
    println("changability score: <changeScore>");
    println("testability score: <testScore>\n");
    println("Overall maintainability score: <maintainScore>");
    
    
}



