/*global describe*/
/*global require*/
/*global module*/
/*global it*/
/*global console*/
/*global process*/

var Tableau = require("./Tableau.js");

// From https://epxx.co/artigos/ludecomp.html
Tableau.prototype.computePermutation = function (B) {
	var height = B.length;

	var tmpRow = new Array(height);
	for (var i = 0; i < height; i++) {
		tmpRow[i] = 0;
	}

	var P = new Array(height);
	for (i = 0; i < height; i++){
		P[i] = tmpRow.slice();
		P[i][i] = 1;
	}

	var exchanges = 0;

	for (var j = 0; j < height; ++j) {
		var row = j;
		var val = 0;
		for (i = j; i < height; ++i) {
			var cand = Math.abs(B[i][j]);
			if (val < cand) {
				val = cand;
				row = i;
			}
		}
		if (j !== row) {
			++exchanges;
			for (i = 0; i < height; ++i) {
				var tmp = P[j][i];
				P[j][i] = P[row][i];
				P[row][i] = tmp;
			}
		}
	}

	return P;
};

// Doolittle's algorithm.
Tableau.prototype.decompose = function (B) {
	// console.log("BDECOMP", JSON.stringify(B));
	// console.log("######BDECOMPDIAG######");
	// for(var loop = 0; loop < B.length; loop++){
	// console.log(B[loop][loop]);
	// }
	// console.log("######BDECOMP######");
	// for(var loop = 0; loop < B.length; loop++){
	// console.log(JSON.stringify(B[loop]));
	// }
	var height = B.length;

	var tmpRow = new Array(height);
	for (var i = 0; i < height; i++) {
		tmpRow[i] = 0;
	}

	var L = new Array(height);
	var U = new Array(height);
	for (var j = 0; j < height; j++) {
		L[j] = tmpRow.slice();
		U[j] = tmpRow.slice();
	}

	for (i = 0; i < height; i++) {
		L[i][i] = 1;
	}

	for(i = 0; i < height; i++){
		// console.log("##############NEW###########");
		// console.log("Bi", JSON.stringify(B[i]));
		for(j = i; j < height; j++){
			U[i][j] = B[i][j];
			// console.log("Uij BEFORE", U[i][j]);
			for(var k = 0; k < i; k++){
				U[i][j] = U[i][j] - L[i][k] * U[k][j];
				// console.log("ijk", i, j, k);
				// console.log("Uij", U[i][j]);
				// console.log("Lik", L[i][k]);
				// console.log("Ukj", U[k][j]);
			}
			// console.log("#####U", i, j, U[i][j]);
		}
		for (j = i + 1; j < height; j++) {
			L[j][i] = B[j][i];
			for (var l = 0; l < i; l++) {
				L[j][i] = L[j][i] - L[j][l] * U[l][i];
			}
			// console.log("height", height);
			// console.log("ijl", i, j, l);
			// console.log("Lji", JSON.stringify(L[j][i]));
			// console.log("Uii", JSON.stringify(U[i][i]));
			L[j][i] = L[j][i] / U[i][i];
			// console.log("Lji AFTER", JSON.stringify(L[j][i]));
		}
	}

	return [L, U];
};

// From https://en.wikipedia.org/wiki/Triangular_matrix#Algorithm
Tableau.prototype.LUEvaluate = function(L, U, b){
	// Ax = b -> LUx = b. Then y is defined to be Ux
	var i = 0;
	var j = 0;
	var n = b.length;
	var x = new Array(n);
	var y = new Array(n);

	// Forward solve Ly = b
	for (i = 0; i < n; i++){
		y[i] = b[i];
		for (j = 0; j < i; j++){
			y[i] -= L[i][j] * y[j];
		}
		y[i] /= L[i][i];
	}

	var invLXa_q = y.slice();

	// Backward solve Ux = y
	for (i = n - 1; i >= 0; i--){
		x[i] = y[i];
		for (j = i + 1; j < n; j++){
			x[i] -= U[i][j] * x[j];
		}
		x[i] /= U[i][i];
	}
	return [x, invLXa_q];
};

function transposeMatrix(M){
	var width = M.length;
	var height = M[0].length;

	var tmpRow = new Array(width);

	var M_T = new Array(height);
	for(var r = 0; r < height; r++){
		M_T[r] = tmpRow.slice();
		for(var c = 0; c < width; c++){
			M_T[r][c] = M[c][r];
		}
	}

	return M_T;
}

function matrixXMatrix(M1, M2){
	var width = M2[0].length;
	var height = M1.length;

	var tmpRow = new Array(width);
	for(var i = 0; i < width; i++){
		tmpRow[i] = 0;
	}

	var M = new Array(height);
	for(i = 0; i < height; i++){
		M[i] = tmpRow.slice();
	}

	for(i = 0; i < M1.length; i++){
		for(var j = 0; j < M2[0].length; j++){
			for(var k = 0; k < M2.length; k++){
				M[i][j] += M1[i][k] * M2[k][j];
			}
		}
	}

	return M;
}

function matrixXVector(M, V){
	var height = M.length;

	var vect = new Array(height);
	for(var i = 0; i < height; i++){
		vect[i] = 0;
	}

	for(i = 0; i < height; i++){
		for(var j = 0; j < M[0].length; j++){
			vect[i] += M[i][j] * V[j];
		}
	}

	return vect;
}

// In some cases it is necessary to permute the basis to make it LU decomposable
// not used as of now since the phase 1 gives the identity as the basis
Tableau.prototype.permuteMatrix = function(P){
	var N = this.matrix;

	var width = N[0].length - 1;
	var height = P.length;

	var M = new Array(height);
	for(var i = 0; i < height; i++){
		M[i] = N[i+1].slice(1);
	}

	for(i = 0; i < P.length; i++){
		for(var j = 0; j < N[0].length-1; j++){
			N[i+1][j+1] = 0;
			for(var k = 0; k < N.length-1; k++){
				N[i+1][j+1] += P[i][k] * M[k][j];
			}
		}
	}
};

Tableau.prototype.updateLU = function(L, U, invLXa_q, pivotIndex){
	var size = L.length;

	for(var i = 0; i < size; i++){
		U[i][pivotIndex] = invLXa_q[i];
	}

	var tmpRow = new Array(size);
	for(i = 0; i < size; i++){
		tmpRow[i] = 0;
	}

	var M = new Array(size);
	for(i = 0; i < size; i++){
		M[i] = tmpRow.slice();
		M[i][i] = 1;
	}

	// console.log("U in");
	// for(i = 0; i < U.length; i++){
	// var str = "";
	// for(j = 0; j < U[0].length; j++){
	// str += U[i][j] + " ";
	// }
	// console.log(str);
	// }
	// console.log("\n");

	for(i = pivotIndex + 1; i < size; i++){
		M[i][pivotIndex] = -U[i][pivotIndex] / U[pivotIndex][pivotIndex];
	}

	U = matrixXMatrix(M, U);

	// for(i = 0; i < size; i++){
	// console.log("M", JSON.stringify(M[i]));
	// }
	// console.log("\n");
	//
	// console.log("U in after");
	// for(i = 0; i < U.length; i++){
	// var str = "";
	// for(j = 0; j < U[0].length; j++){
	// str += U[i][j] + " ";
	// }
	// console.log(str);
	// }
	// console.log("\n");

	for(i = pivotIndex + 1; i < size; i++){
		M[i][pivotIndex] = -M[i][pivotIndex];
	}

	L = matrixXMatrix(L, M);

	return [L, U];
};

Tableau.prototype.LUSimplexPhase1 = function () {
    var debugCheckForCycles = this.model.checkForCycles;
    var varIndexesCycle = [];

    var matrix = this.matrix;
    var rhsColumn = this.rhsColumn;
    var lastColumn = this.width - 1;
    var lastRow = this.height - 1;

    var unrestricted;
    var iterations = 0;
    while (true) {
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

        console.log("matrix");
        for(var i = 0; i < this.matrix.length; i++){
            var tmpstr = "";
            for(var j = 0; j < this.matrix[0].length; j++){
                tmpstr += this.matrix[i][j].toFixed(2) + "\t";
            }
            console.log(tmpstr);
        }
        console.log("\n");

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

        this.pivot(leavingRowIndex, enteringColumn);
        iterations += 1;
    }
};

Tableau.prototype.LUSimplexPhase2 = function(){
	// console.log("NAME", this.model.name);
	var debugCheckForCycles = this.model.checkForCycles;
    var varIndexesCycle = [];
	var iter = 0;
	var precision = this.precision;

	var N = this.matrix;

	var originalZ = N[0][0];

	// var BIdx = this.varIndexByRow;
	// BIdx.splice(0, 1);
	// var NIdx = this.varIndexByCol;
	// NIdx.splice(0, 1);

	// initialize basis
	var tmpRow = new Array(this.height-1);
	for (var i = 0; i < tmpRow.length; i++) {
		tmpRow[i] = 0;
	}

	var B = new Array(this.height-1);
	for (var j = 0; j < B.length; j++) {
		B[j] = tmpRow.slice();
		B[j][j] = 1;
	}

	var cB = tmpRow.slice();

	var nOptionalObjectives = this.optionalObjectives.length;

	var cBOptionals;
	if(nOptionalObjectives > 0){
		cBOptionals = new Array(nOptionalObjectives);
		for (i = 0; i < cBOptionals.length; i++) {
			cBOptionals[i] = tmpRow.slice();
		}
	}

	// var cN = new Array(this.width-1);
	// for(var i = 0; i < cN.length; i++){
	// cN[i] = -N[0][i+1];
	// }
	var cN = N[0].slice(1);

	var b = new Array(this.height-1);
	for(var v = 0; v < b.length; v++){
		b[v] = N[v+1][0];
	}

	console.log("BIdx before", JSON.stringify(this.varIndexByRow));
	console.log("NIdx before", JSON.stringify(this.varIndexByCol));
	console.log("N before", JSON.stringify(N));
	console.log("cN before", JSON.stringify(cN));
	console.log("b before", JSON.stringify(b));
	console.log("z before", JSON.stringify(originalZ));

	var LU = this.decompose(B);
	var LU_T = this.decompose(transposeMatrix(B));

	// var P = this.computePermutation(B);
	// // var idt = B.slice();
	// // P = idt;
	// B = matrixXMatrix(P, B);
	// var B_T = transposeMatrix(B);
	// var LU = this.decompose(B);
	// var LU_T = this.decompose(B_T);
	// // b = matrixXVector(P, b);
	// BIdx = matrixXVector(P, BIdx);
	// this.permuteMatrix(P);

	var updated_b = this.LUEvaluate(LU[0], LU[1], b)[0];

	// console.log("N right after", JSON.stringify(N));
	//
	// throw new Error();

	var unrestricted;

	while(true){
		console.log("New iteration\n\n");
		var rCost = precision;
		var enteringColumn = -1;

		var optionalCostsColumns = null;
		if (nOptionalObjectives > 0) {
			optionalCostsColumns = [];
		}

		var isReducedCostNegative = false;

		console.log("lu1", JSON.stringify(LU[0]));
		console.log("lu2", JSON.stringify(LU[1]));
		console.log("lu1", JSON.stringify(LU_T[0]));
		console.log("lu2", JSON.stringify(LU_T[1]));
		// console.log("cBBBBBBBB", JSON.stringify(cB));
		// console.log("LU1", LU_T[0]);
		// console.log("LU2", LU_T[1]);
		var u = this.LUEvaluate(LU_T[0], LU_T[1], cB)[0];

		console.log("u", u);

		var updated_cN = cN.slice();
		var tmpVect = new Array(cN.length);
		for(i = 0; i < tmpVect.length; i++){
			tmpVect[i] = 0;
		}
		for(i = 0; i < tmpVect.length; i++){
			for(j = 0; j < u.length; j++){
				tmpVect[i] += u[j]*N[j+1][i+1];
			}
		}
		// console.log("tmpVect", JSON.stringify(tmpVect));
		for(var rc = 0; rc < updated_cN.length; rc++){
			updated_cN[rc] -= tmpVect[rc];
		}
		console.log("updated_cN", JSON.stringify(updated_cN));

		for(var c = 0; c < updated_cN.length; c++){
			// console.log("yay_rC", rCost);
			// console.log("yay_cN", updated_cN[c]);
			if(nOptionalObjectives > 0 && -precision < updated_cN[c] && updated_cN[c] < precision){
				optionalCostsColumns.push(c);
				continue;
			}

			if(unrestricted && updated_cN[c] < 0){
				if(-updated_cN[c] > rCost){
					rCost = -updated_cN[c];
					enteringColumn = c;
					isReducedCostNegative = true;
				}
				continue;
			}

			if(updated_cN[c] > rCost){
				rCost = updated_cN[c];
				enteringColumn = c;
				isReducedCostNegative = false;
			}
		}

		if(nOptionalObjectives > 0){
			console.log("optional");
			var optionalCostsColumns2 = [];
			var o = 0;

			while(enteringColumn === -1 && optionalCostsColumns.length > 0 && o < nOptionalObjectives){
				var tmp_cN = this.optionalObjectives[o].reducedCosts.slice(1);
				for(i = 0; i < tmpVect.length; i++){
					tmpVect[i] = 0;
				}
				for(i = 0; i < tmpVect.length; i++){
					for(j = 0; j < u.length; j++){
						tmpVect[i] += u[j]*N[j+1][i+1];
					}
				}
				for(rc = 0; rc < updated_cN.length; rc++){
					tmp_cN[rc] -= tmpVect[rc];
				}

				rCost = precision;

				var tmpCost;
				for(i = 0; i < optionalCostsColumns.length; i++){
					c = optionalCostsColumns[i];
					tmpCost = tmp_cN[c];
					unrestricted = this.unrestrictedVars[this.varIndexByCol[c]] === true;

					if(-precision < tmpCost && tmpCost < precision){
						optionalCostsColumns2.push(c);
						continue;
					}

					if(unrestricted && tmpCost < 0){
						if(-tmpCost > rCost){
							rCost = -tmpCost;
							enteringColumn = c;
							isReducedCostNegative = true;
						}
						continue;
					}

					if(tmpCost > rCost){
						rCost = tmpCost;
						enteringColumn = c;
						isReducedCostNegative = false;
					}
				}
				optionalCostsColumns = optionalCostsColumns2;
				o++;
			}
		}

		if (enteringColumn === -1) {
			// BIdx.unshift(-1);
			// NIdx.unshift(-1);
			// this.varIndexByRow = BIdx;
			// this.varIndexByCol = NIdx;
            this.setEvaluation();
			// var M = [
			// [0, -2, 6],
			// [-2, -5, 8],
			// [5, -10, -4]
			// ];
			// console.log("########TAYST########");
			// console.log(JSON.stringify(this.decompose(matrixXMatrix(this.computePermutation(M), M))));
            return iter;
        }

		var aq = new Array(this.height-1);
		for(var r = 0; r < aq.length; r++){
			aq[r] = N[r+1][enteringColumn+1];
		}
		// console.log("aq", aq);
		var aqInfo = this.LUEvaluate(LU[0], LU[1], aq);
		var updated_aq = aqInfo[0];
		console.log("updated_aq", updated_aq);
		var invLXa_q = aqInfo[1];
		// console.log("invLXa_q", invLXa_q, "\n");



		var minRatio = Infinity;
		var leavingRow = -1;

        for (r = 0; r < updated_b.length; r++) {
            var rhsValue = updated_b[r];
            var colValue = updated_aq[r];

            if (-precision < colValue && colValue < precision) {
                continue;
            }

            if (colValue > 0 && precision > rhsValue && rhsValue > -precision) {
                minRatio = 0;
                leavingRow = r;
                break;
            }

            var ratio = isReducedCostNegative ? -rhsValue / colValue : rhsValue / colValue;
            if (ratio > precision && minRatio > ratio) {
                minRatio = ratio;
                leavingRow = r;
            }
        }

		if (minRatio === Infinity) {
			// BIdx.unshift(-1);
			// NIdx.unshift(-1);
            // optimal value is -Infinity
            this.evaluation = -Infinity;
            this.bounded = false;
            this.unboundedVarIndex = this.varIndexByCol[enteringColumn+1];
            return iter;
        }

		if(debugCheckForCycles){
            varIndexesCycle.push([this.varIndexByRow[leavingRow+1], this.varIndexByCol[enteringColumn+1]]);

            var cycleData = this.checkForCycles(varIndexesCycle);
            if(cycleData.length > 0){
                console.log("Cycle in phase 2");
                console.log("Start :", cycleData[0]);
                console.log("Length :", cycleData[1]);
                throw new Error();
            }
        }

		console.log("entering", this.varIndexByCol[enteringColumn+1]);
		// console.log("rc", rCost);
		console.log("leaving", this.varIndexByRow[leavingRow+1]);
		console.log("min ratio", minRatio);

		for(r = 0; r < updated_b.length; r++){
			updated_b[r] -= minRatio * updated_aq[r];
			N[r+1][0] = updated_b[r];
		}
		updated_b[leavingRow] = minRatio;
		N[leavingRow+1][0] = updated_b[leavingRow];

		console.log("b", JSON.stringify(updated_b));

		////////////////////////////

		// var tmpIdx = BIdx[leavingRow];
		// BIdx[leavingRow] = NIdx[enteringColumn];
		// NIdx[enteringColumn] = tmpIdx;

		// console.log("//////////////////////////////////");
		//
		// console.log("leavingRow", leavingRow + 1);
		// console.log("enteringColumn", enteringColumn + 1);

		var leavingBasicIndex = this.varIndexByRow[leavingRow + 1];
		var enteringBasicIndex = this.varIndexByCol[enteringColumn + 1];

		// console.log("leavingBasicIndex", leavingBasicIndex);
		// console.log("enteringBasicIndex", enteringBasicIndex);

		this.varIndexByRow[leavingRow + 1] = enteringBasicIndex;
		this.varIndexByCol[enteringColumn + 1] = leavingBasicIndex;

		this.rowByVarIndex[enteringBasicIndex] = leavingRow + 1;
		this.rowByVarIndex[leavingBasicIndex] = -1;

		this.colByVarIndex[enteringBasicIndex] = -1;
		this.colByVarIndex[leavingBasicIndex] = enteringColumn + 1;

		// console.log("//////////////////////////////////");

		////////////////////////////

		// console.log("B", JSON.stringify(B));
		// console.log("N", JSON.stringify(N));
		// console.log("\n");

		var pivot = N[leavingRow+1][enteringColumn+1];
		// console.log("pivot", pivot);

		// Update B and N
		for(r = 0; r < B.length; r++){
			var tmpVal = B[r][leavingRow];

			B[r][leavingRow] = N[r+1][enteringColumn+1];

			N[r+1][enteringColumn+1] = tmpVal;
		}
		N[0][enteringColumn+1] = cB[leavingRow];

		// console.log("enteringColumn", enteringColumn);
		// console.log("leavingRow", leavingRow);
		// console.log("cB", JSON.stringify(cB));
		// console.log("cN", JSON.stringify(cN));
		// console.log("\n");

		var tmp_cNCost = cN[enteringColumn];
		cN[enteringColumn] = cB[leavingRow];
		cB[leavingRow] = tmp_cNCost;

		console.log("cB", JSON.stringify(cB));
		console.log("cN", JSON.stringify(cN));

		if(nOptionalObjectives > 0){
			for (i = 0; i < cBOptionals.length; i++) {
				tmp_cNCost = this.optionalObjectives[i][enteringColumn+1];
				this.optionalObjectives[i][enteringColumn+1] = cBOptionals[i][leavingRow];
				cBOptionals[i][leavingRow] = tmp_cNCost;
			}
		}


		console.log("B");
		for(i = 0; i < B.length; i++){
		var str = "";
		for(j = 0; j < B.length; j++){
		str += B[i][j] + " ";
		}
		console.log(str);
		}
		console.log("\n");
		console.log("N");
		for(i = 0; i < N.length; i++){
		var str = "";
		for(j = 0; j < N.length; j++){
		str += N[i][j] + " ";
		}
		console.log(str);
		}
		console.log("\n");
		// console.log("L");
		// for(i = 0; i < LU[0].length; i++){
		// var str = "";
		// for(j = 0; j < LU[0][0].length; j++){
		// str += LU[0][i][j] + " ";
		// }
		// console.log(str);
		// }
		// console.log("\n");
		// console.log("U");
		// for(i = 0; i < LU[1].length; i++){
		// var str = "";
		// for(j = 0; j < LU[1][0].length; j++){
		// str += LU[1][i][j] + " ";
		// }
		// console.log(str);
		// }
		// console.log("\n");




		// LU = this.decompose(B);
		// // LU_T = this.decompose(transposeMatrix(B));
		// LU_T[0] = transposeMatrix(LU[0]);
		// LU_T[1] = transposeMatrix(LU[1]);

		LU = this.updateLU(LU[0], LU[1], invLXa_q, leavingRow);
		LU_T[0] = transposeMatrix(LU[0]);
		LU_T[1] = transposeMatrix(LU[1]);

		console.log("L after");
		for(i = 0; i < LU[0].length; i++){
		var str = "";
		for(j = 0; j < LU[0][0].length; j++){
		str += LU[0][i][j] + " ";
		}
		console.log(str);
		}
		console.log("\n");
		console.log("U after");
		for(i = 0; i < LU[1].length; i++){
		var str = "";
		for(j = 0; j < LU[1][0].length; j++){
		str += LU[1][i][j] + " ";
		}
		console.log(str);
		}
		console.log("\n");

		console.log("L_T after");
		for(i = 0; i < LU_T[0].length; i++){
		var str = "";
		for(j = 0; j < LU_T[0][0].length; j++){
		str += LU_T[0][i][j] + " ";
		}
		console.log(str);
		}
		console.log("\n");
		console.log("U_T after");
		for(i = 0; i < LU_T[1].length; i++){
		var str = "";
		for(j = 0; j < LU_T[1][0].length; j++){
		str += LU_T[1][i][j] + " ";
		}
		console.log(str);
		}
		console.log("\n");
		console.log("\n");





		// P = this.computePermutation(B);
		// // P = idt;
		// B = matrixXMatrix(P, B);
		// B_T = transposeMatrix(B);
		// LU = this.decompose(B);
		// LU_T = this.decompose(B_T);
		// // updated_b = matrixXVector(P, updated_b);
		// BIdx = matrixXVector(P, BIdx);
		// // cB = matrixXVector(P, cB);
		// this.permuteMatrix(P);









		iter++;

		var z = 0;
		for(i = 0; i < updated_b.length; i++){
			z += updated_b[i]*cB[i];
		}
		N[0][0] = z - originalZ;
		// // console.log("BIdx", BIdx);
		// console.log("B", JSON.stringify(B));
		// console.log("new cB", JSON.stringify(cB));
		// // console.log("NIdx", NIdx);
		// console.log("N", JSON.stringify(N));
		// console.log("new cN", JSON.stringify(cN));
		// console.log("updated_b", JSON.stringify(updated_b));
		// console.log("z =", z);
		// console.log("\n\n");

		// if(iter === 3){
		// throw new Error();
		// }
	}
};
