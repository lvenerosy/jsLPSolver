/*global describe*/
/*global require*/
/*global module*/
/*global it*/
/*global console*/
/*global process*/

var Tableau = require("./Tableau.js");
var LU = require("./LUDecomposition.js");

//-------------------------------------------------------------------
// Function: solve
// Detail: Main function, linear programming solver
//-------------------------------------------------------------------
Tableau.prototype.simplex = function () {
    // Bounded until proven otherwise
    this.bounded = true;

    // Execute Phase 1 to obtain a Basic Feasible Solution (BFS)
    if (this.model.useRevisedSimplex) {
        // console.log("using revised method");
        this.LUSimplexPhase1();
    }
    else{
        this.phase1();
    }


    // Execute Phase 2
    if (this.feasible === true) {
        this.tmpIter++;
        // Running simplex on Initial Basic Feasible Solution (BFS)
        // N.B current solution is feasible
        if (this.model.useRevisedSimplex) {
            this.LUSimplexPhase2();
        }
        else{
            this.phase2();
        }
    }
    // this.displayTableau();
    //
    // console.log();
    // console.log("variables", this.variablesPerIndex);
    // console.log("varIndexByRow", this.varIndexByRow);
    // console.log("varIndexByCol", this.varIndexByCol);
    // console.log("rowByVarIndex", this.rowByVarIndex);
    // console.log("colByVarIndex", this.colByVarIndex);

    // console.log("SUCCESS");

    return this;
};

//-------------------------------------------------------------------
// Description: Convert a non standard form tableau
//              to a standard form tableau by eliminating
//              all negative values in the Right Hand Side (RHS)
//              This results in a Basic Feasible Solution (BFS)
//
//-------------------------------------------------------------------
Tableau.prototype.phase1 = function () {
    // console.log("##########PHASE 1##########");
    // this.displayTableau();
    var debugCheckForCycles = this.model.checkForCycles;
    var varIndexesCycle = [];

    var matrix = this.matrix;
    var rhsColumn = this.rhsColumn;
    var lastColumn = this.width - 1;
    var lastRow = this.height - 1;

    var unrestricted;
    var iterations = 0;
    while (true) {
        // console.log("PHASE 1 ITERATION :", iterations);
        var debugLog = false;
        // if (iterations === 0) {
        //     this.displayTableau();
        // }
        // Selecting leaving variable (feasibility condition):
        // Basic variable with most negative value
        var leavingRowIndex = 0;
        var rhsValue = -this.precision;
        for (var r = 1; r <= lastRow; r++) {
            unrestricted = this.unrestrictedVars[this.varIndexByRow[r]] === true;
            if (unrestricted) {
                continue;
            }

            var value = matrix[r][rhsColumn];
            if (value < rhsValue) {
                rhsValue = value;
                leavingRowIndex = r;
            }
        }

        // If nothing is strictly smaller than 0; we're done with phase 1.
        if (leavingRowIndex === 0) {
            // Feasible, champagne!
            this.feasible = true;
            return iterations;
        }

        // Selecting entering variable
        var enteringColumn = 0;
        var maxQuotient = -Infinity;
        var costRow = matrix[0];
        var leavingRow = matrix[leavingRowIndex];
        for (var c = 1; c <= lastColumn; c++) {
            var coefficient = leavingRow[c];
            if (-this.precision < coefficient && coefficient < this.precision) {
                continue;
            }

            unrestricted = this.unrestrictedVars[this.varIndexByCol[c]] === true;
            if (unrestricted || coefficient < -this.precision) {
                var quotient = -costRow[c] / coefficient;
                if (maxQuotient < quotient) {
                    maxQuotient = quotient;
                    enteringColumn = c;
                }
            }
        }

        if (enteringColumn === 0) {
            // Not feasible
            this.feasible = false;
            return iterations;
        }

        if(debugCheckForCycles){
            varIndexesCycle.push([this.varIndexByRow[leavingRowIndex], this.varIndexByCol[enteringColumn]]);

            var cycleData = this.checkForCycles(varIndexesCycle);
            if(cycleData.length > 0){
                console.log("Cycle in phase 1");
                console.log("Start :", cycleData[0]);
                console.log("Length :", cycleData[1]);
                throw new Error();
            }
        }

        var i;
        var tmpcol = [];
        for (i = 1; i < this.height; i++) {
            tmpcol.push(matrix[i][enteringColumn]);
        }
        // this.debugLog(function () { console.log("HERE entering col", enteringColumn, ":", tmpcol); }, debugLog);
        // this.debugLog(function () { console.log("HERE leaving row", leavingRowIndex, ":", matrix[leavingRowIndex].slice(1)); }, debugLog);


        tmpcol = [];
        for (i = 1; i < this.height; i++) {
            tmpcol.push(matrix[i][0]);
        }
        // this.debugLog(function () { console.log("HERE b", tmpcol); }, debugLog);


        this.pivot(leavingRowIndex, enteringColumn);
        iterations += 1;

        // this.displayTableau();

    }
};

//-------------------------------------------------------------------
// Description: Apply simplex to obtain optimal solution
//              used as phase2 of the simplex
//
//-------------------------------------------------------------------
Tableau.prototype.phase2 = function () {
    // console.log("##########PHASE 2##########");
    // this.displayTableau();

    var debugCheckForCycles = this.model.checkForCycles;
    var varIndexesCycle = [];

    var matrix = this.matrix;
    var rhsColumn = this.rhsColumn;
    var lastColumn = this.width - 1;
    var lastRow = this.height - 1;

    var precision = this.precision;
    var nOptionalObjectives = this.optionalObjectives.length;
    var optionalCostsColumns = null;

    var iterations = 0;
    var reducedCost, unrestricted;
    while (true) {
        // console.log("PHASE 2 ITERATION :", iterations);
        var debugLog = false;

        var costRow = matrix[this.costRowIndex];

        // Selecting entering variable (optimality condition)
        if (nOptionalObjectives > 0) {
            optionalCostsColumns = [];
        }

        var enteringColumn = 0;
        var enteringValue = precision;
        var isReducedCostNegative = false;
        for (var c = 1; c <= lastColumn; c++) {
            reducedCost = costRow[c];
            unrestricted = this.unrestrictedVars[this.varIndexByCol[c]] === true;

            if (nOptionalObjectives > 0 && -precision < reducedCost && reducedCost < precision) {
                optionalCostsColumns.push(c);
                continue;
            }

            if (unrestricted && reducedCost < 0) {
                if (-reducedCost > enteringValue) {
                    enteringValue = -reducedCost;
                    enteringColumn = c;
                    isReducedCostNegative = true;
                }
                continue;
            }

            if (reducedCost > enteringValue) {
                enteringValue = reducedCost;
                enteringColumn = c;
                isReducedCostNegative = false;
            }
        }

        var i;
        if (nOptionalObjectives > 0) {
            // There exist optional improvable objectives
            for (i = 0; i < nOptionalObjectives; i++) {
				var tmpocost = this.optionalObjectives[i].reducedCosts.slice(1);
                var optionalObjVal = [this.optionalObjectives[i].reducedCosts[0]];
				// this.debugLog(function () { console.log("optional", i, optionalObjVal, tmpocost); }, debugLog);
			}
            var o = 0;
            while (enteringColumn === 0 && optionalCostsColumns.length > 0 && o < nOptionalObjectives) {
                var optionalCostsColumns2 = [];
                var reducedCosts = this.optionalObjectives[o].reducedCosts;

                enteringValue = precision;

                for (i = 0; i < optionalCostsColumns.length; i++) {
                    c = optionalCostsColumns[i];

                    reducedCost = reducedCosts[c];
                    unrestricted = this.unrestrictedVars[this.varIndexByCol[c]] === true;

                    if (-precision < reducedCost && reducedCost < precision) {
                        optionalCostsColumns2.push(c);
                        continue;
                    }

                    if (unrestricted && reducedCost < 0) {
                        if (-reducedCost > enteringValue) {
                            enteringValue = -reducedCost;
                            enteringColumn = c;
                            isReducedCostNegative = true;
                        }
                        continue;
                    }

                    if (reducedCost > enteringValue) {
                        enteringValue = reducedCost;
                        enteringColumn = c;
                        isReducedCostNegative = false;
                    }
                }
                optionalCostsColumns = optionalCostsColumns2;
                o += 1;
            }
        }

        var tmpcol = [];
        for (i = 1; i < this.height; i++) {
            tmpcol.push(matrix[i][0]);
        }
        // this.debugLog(function () { console.log("HERE b", tmpcol); }, debugLog);


        // If no entering column could be found we're done with phase 2.
        if (enteringColumn === 0) {
            this.setEvaluation();
            return iterations;
        }

        // Selecting leaving variable
        var leavingRow = 0;
        var minQuotient = Infinity;

        var varIndexByRow = this.varIndexByRow;

        for (var r = 1; r <= lastRow; r++) {
            // this.debugLog(function () { console.log("minQuotient", minQuotient); }, debugLog);
            var row = matrix[r];
            var rhsValue = row[rhsColumn];
            var colValue = row[enteringColumn];

            if (-precision < colValue && colValue < precision) {
                continue;
            }

            if (colValue > 0 && precision > rhsValue && rhsValue > -precision) {
                minQuotient = 0;
                leavingRow = r;
                break;
            }

            var quotient = isReducedCostNegative ? -rhsValue / colValue : rhsValue / colValue;
            if (quotient > precision && minQuotient > quotient) {
                minQuotient = quotient;
                leavingRow = r;
            }
        }
        // console.log("minQuotient", minQuotient);

        tmpcol = [];
        for (i = 1; i < this.height; i++) {
            tmpcol.push(matrix[i][enteringColumn]);
        }
        // this.debugLog(function () { console.log("HERE entering col", enteringColumn, ":", tmpcol); }, debugLog);
        // this.debugLog(function () { console.log("HERE leaving row", leavingRow, ":", matrix[leavingRow].slice(1)); }, debugLog);



        if (minQuotient === Infinity) {
            // optimal value is -Infinity
            this.evaluation = -Infinity;
            this.bounded = false;
            this.unboundedVarIndex = this.varIndexByCol[enteringColumn];
            return iterations;
        }

        if(debugCheckForCycles){
            varIndexesCycle.push([this.varIndexByRow[leavingRow], this.varIndexByCol[enteringColumn]]);

            var cycleData = this.checkForCycles(varIndexesCycle);
            if(cycleData.length > 0){
                console.log("Cycle in phase 2");
                console.log("Start :", cycleData[0]);
                console.log("Length :", cycleData[1]);
                throw new Error();
            }
        }

        this.pivot(leavingRow, enteringColumn, true);
        iterations += 1;

        // this.displayTableau();
    }
};

// Array holding the column indexes for which the value is not null
// on the pivot row
// Shared by all tableaux for smaller overhead and lower memory usage
var nonZeroColumns = [];
//-------------------------------------------------------------------
// Description: Execute pivot operations over a 2d array,
//          on a given row, and column
//
//-------------------------------------------------------------------
Tableau.prototype.pivot = function (pivotRowIndex, pivotColumnIndex) {
    var matrix = this.matrix;

    var quotient = matrix[pivotRowIndex][pivotColumnIndex];

    var lastRow = this.height - 1;
    var lastColumn = this.width - 1;

    // console.log("//////////////////////////////////");
    //
    // console.log("leavingRow", pivotRowIndex);
    // console.log("enteringColumn", pivotColumnIndex);

    var leavingBasicIndex = this.varIndexByRow[pivotRowIndex];
    var enteringBasicIndex = this.varIndexByCol[pivotColumnIndex];

    // console.log("leavingBasicIndex", leavingBasicIndex);
    // console.log("enteringBasicIndex", enteringBasicIndex);

    this.varIndexByRow[pivotRowIndex] = enteringBasicIndex;
    this.varIndexByCol[pivotColumnIndex] = leavingBasicIndex;

    this.rowByVarIndex[enteringBasicIndex] = pivotRowIndex;
    this.rowByVarIndex[leavingBasicIndex] = -1;

    this.colByVarIndex[enteringBasicIndex] = -1;
    this.colByVarIndex[leavingBasicIndex] = pivotColumnIndex;

    // console.log("//////////////////////////////////");

    // Divide everything in the target row by the element @
    // the target column
    var pivotRow = matrix[pivotRowIndex];
    var nNonZeroColumns = 0;
    for (var c = 0; c <= lastColumn; c++) {
        if (pivotRow[c] !== 0) {
            pivotRow[c] /= quotient;
            nonZeroColumns[nNonZeroColumns] = c;
            nNonZeroColumns += 1;
        }
    }
    pivotRow[pivotColumnIndex] = 1 / quotient;

    // for every row EXCEPT the pivot row,
    // set the value in the pivot column = 0 by
    // multiplying the value of all elements in the objective
    // row by ... yuck... just look below; better explanation later
    var coefficient, i, v0;
    var precision = this.precision;
    for (var r = 0; r <= lastRow; r++) {
        var row = matrix[r];
        if (r !== pivotRowIndex) {
            coefficient = row[pivotColumnIndex];
            // No point Burning Cycles if
            // Zero to the thing
            if (coefficient !== 0) {
                for (i = 0; i < nNonZeroColumns; i++) {
                    c = nonZeroColumns[i];
                    // No point in doing math if you're just adding
                    // Zero to the thing
                    v0 = pivotRow[c];
                    if (v0 !== 0) {
                        row[c] = row[c] - coefficient * v0;
                        // if(i === 0){
                        //     console.log("diff_"+i, coefficient * v0);
                        //     console.log("val_"+i, v0);
                        //     console.log("minRatio", coefficient);
                        // }
                    }
                }

                row[pivotColumnIndex] = -coefficient / quotient;
            }
        }
    }

    var nOptionalObjectives = this.optionalObjectives.length;
    if (nOptionalObjectives > 0) {
        for (var o = 0; o < nOptionalObjectives; o += 1) {
            var reducedCosts = this.optionalObjectives[o].reducedCosts;
            coefficient = reducedCosts[pivotColumnIndex];
            if (coefficient !== 0) {
                for (i = 0; i < nNonZeroColumns; i++) {
                    c = nonZeroColumns[i];
                    v0 = pivotRow[c];
                    if (v0 !== 0) {
                        reducedCosts[c] = reducedCosts[c] - coefficient * v0;
                    }
                }

                reducedCosts[pivotColumnIndex] = -coefficient / quotient;
            }
        }
    }
};



Tableau.prototype.checkForCycles = function (varIndexes) {
    for (var e1 = 0; e1 < varIndexes.length - 1; e1++) {
        for (var e2 = e1 + 1; e2 < varIndexes.length; e2++) {
            var elt1 = varIndexes[e1];
            var elt2 = varIndexes[e2];
            if (elt1[0] === elt2[0] && elt1[1] === elt2[1]) {
                if (e2 - e1 > varIndexes.length - e2) {
                    break;
                }
                var cycleFound = true;
                for (var i = 1; i < e2 - e1; i++) {
                    var tmp1 = varIndexes[e1+i];
                    var tmp2 = varIndexes[e2+i];
                    if(tmp1[0] !== tmp2[0] || tmp1[1] !== tmp2[1]) {
                        cycleFound = false;
                        break;
                    }
                }
                if (cycleFound) {
                    return [e1, e2 - e1];
                }
            }
        }
    }
    return [];
};
