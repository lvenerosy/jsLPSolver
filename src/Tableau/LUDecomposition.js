/*global describe*/
/*global require*/
/*global module*/
/*global it*/
/*global console*/
/*global process*/

var Tableau = require("./Tableau.js");



// Doolittle's algorithm.
Tableau.prototype.decompose = function (B) {
	var height = this.nextBasisIndex;

	// var tmpRow = new Array(height);
	// for (var i = 0; i < height; i++) {
	// 	tmpRow[i] = 0;
	// }
	//
	// var L = new Array(height);
	// var U = new Array(height);
	// for (var j = 0; j < height; j++) {
	// 	L[j] = tmpRow.slice();
	// 	U[j] = tmpRow.slice();
	// }

	var L = this.tmpL;
	var U = this.tmpU;

	for (i = 0; i < height; i++) {
		L[i][i] = 1;
	}

	for (i = 0; i < height; i++) {
		for (j = i; j < height; j++) {
			U[i][j] = B[i][j];
			for (var k = 0; k < i; k++) {
				U[i][j] = U[i][j] - L[i][k] * U[k][j];
			}
		}

		for (j = i + 1; j < height; j++) {
			L[j][i] = B[j][i];
			for (var l = 0; l < i; l++) {
				L[j][i] = L[j][i] - L[j][l] * U[l][i];
			}
			L[j][i] = L[j][i] / U[i][i];
		}
	}
	return [L, U];
};

Tableau.prototype.divideRowByFactor = function (rowIndex, factor) {
	if (factor === 0) {
		throw new Error("Dividing by zero");
	}
	var B = this.basis;
	var N = this.matrix;
	var BHeight = this.nextBasisIndex;
	for (var i = 0; i < BHeight; i++) {
		B[rowIndex - 1][i] /= factor;
	}
	var NWidth = this.width;
	for (i = 0; i < NWidth; i++) {
		N[rowIndex][i] /= factor;
	}

	this.originalRHS[rowIndex - 1] /= factor;
	// this.currentRHS[rowIndex - 1] /= factor;
};

Tableau.prototype.multiplyRowByFactor = function (rowIndex, factor) {
	if (factor === 0) {
		throw new Error("Multiplying by zero");
	}
	var B = this.basis;
	var N = this.matrix;
	var BHeight = this.nextBasisIndex;
	for (var i = 0; i < BHeight; i++) {
		B[rowIndex - 1][i] *= factor;
	}
	var NWidth = this.width;
	for (i = 0; i < NWidth; i++) {
		N[rowIndex][i] *= factor;
	}

	this.originalRHS[rowIndex - 1] *= factor;
	// this.currentRHS[rowIndex - 1] *= factor;
};

Tableau.prototype.decompose2 = function (B, b) {
	var height = this.nextBasisIndex;
	var i, j, k;
	var LU = new Array(height);
	for (i = 0; i < height; i++) {
		LU[i] = B[i].slice();
	}
	// Rook pivoting algorithm
	// for each diagonal element
	for (i = 0; i < height - 1; i++) {
		var biggerValueExists = true;
		var biggestValueCol = i;
		var biggestValueRow = i;
		// for each element of the sub matrix of B from i to height
		while (biggerValueExists) {
			biggerValueExists = false;
			// search in current best column the best row
			for (j = i; j < height; j++) {
				if (Math.abs(LU[j][biggestValueCol]) > Math.abs(LU[biggestValueRow][biggestValueCol])) {
					biggestValueRow = j;
				}
			}
			// search in current best row the best column
			for (j = i; j < height; j++) {
				if (Math.abs(LU[biggestValueRow][j] > Math.abs(LU[biggestValueRow][biggestValueCol]))) {
					biggestValueCol = j;
					biggerValueExists = true;
				}
			}
		}


		var tmp;
		// Now that we found the best element to pivot on, let's pivot
		this.switchRows(i + 1, biggestValueRow + 1);
		if (i !== biggestValueRow) {
			// tmp = b[i];
			// b[i] = b[biggestValueRow];
			// b[biggestValueRow] = tmp;
			for (j = 0; j < height; j++) {
				tmp = LU[biggestValueRow][j];
				LU[biggestValueRow][j] = LU[i][j];
				LU[i][j] = tmp;
			}
		}
		this.switchBasicColumns(i + 1, biggestValueCol + 1);
		if (i !== biggestValueCol) {
			tmp = b[i];
			b[i] = b[biggestValueCol];
			b[biggestValueCol] = tmp;
			for (j = 0; j < height; j++) {
				tmp = LU[j][biggestValueCol];
				LU[j][biggestValueCol] = LU[j][i];
				LU[j][i] = tmp;
			}
		}

		// Update the LU matrix as to get the 0s of the Gaussian Elimination in the column i below the diagonal "of U"
		for (j = i + 1; j < height; j++) {
			if (LU[j][i] !== 0) {
				var factor = LU[j][i] / LU[i][i];
				LU[j][i] = factor;
				for (k = i + 1; k < height; k++) {
					LU[j][k] -= factor * LU[i][k];
				}
			}
		}
	}

	// TODO: change the rest of the code where L and U are still used as separate matrices
	var dummyRow = new Array(height).fill(0);
	var L = new Array(height);
	for (i = 0; i < height; i++) {
		L[i] = dummyRow.slice();
		for (j = 0; j < i; j++) {
			L[i][j] = LU[i][j];
			// LU is used as U
			LU[i][j] = 0;
		}
		L[i][i] = 1;
	}

	return [L, LU];
}

// From https://en.wikipedia.org/wiki/Triangular_matrix#Algorithm
Tableau.prototype.LUEvaluate = function (L, U, b) {
	// Ax = b -> LUx = b. Then y is defined to be Ux
	var i = 0;
	var j = 0;
	var n = this.nextBasisIndex;
	var x = new Array(n);
	var y = new Array(n);

	console.log("new evaluate true", JSON.stringify(b));
	// Forward solve Ly = b
	var ROW = 0;
	for (i = 0; i < n; i++) {
		y[i] = b[i];
		console.log("y", y[i]);
		for (j = 0; j < i; j++) {
			console.log("yy", JSON.stringify(y));
			y[i] -= L[i][j] * y[j];
			console.log("tmpy", y[i], "; y -=", L[i][j], "*", y[j]);
		}
		y[i] /= L[i][i];
		console.log("tmpy", y[i], "; y /=", L[i][i]);
	}
	console.log("debug y", JSON.stringify(y));
	// throw true;

	var invLXa_q = y.slice();

	// Backward solve Ux = y
	for (i = n - 1; i >= 0; i--) {
		x[i] = y[i];
		console.log("x", x[i]);
		for (j = i + 1; j < n; j++) {
			console.log("xx", JSON.stringify(x));
			x[i] -= U[i][j] * x[j];
			console.log("tmpx", x[i], "; x -=", U[i][j], "*", x[j]);
		}
		x[i] /= U[i][i];
		console.log("tmpx", x[i], "; x /=", U[i][i]);
	}
	console.log("debug x", JSON.stringify(x));

	return [x, invLXa_q];
};


Tableau.prototype.reverseLUEvaluate = function (L, U, b) {
	var i = 0;
	var j = 0;
	var n = this.nextBasisIndex;
	var x = b.slice();
	var y = new Array(n);

	for (i = 0; i <= n - 1; i++) {
		x[i] *= U[i][i];
		for (j = n - 1; j >= i + 1; j--) {
			x[i] += U[i][j] * x[j];
		}
		y[i] = x[i];
	}

	for (i = n - 1; i >= 0; i--) {
		y[i] *= L[i][i];
		for (j = i - 1; j >= 0; j--) {
			y[i] += L[i][j] * y[j];
		}
	}

	return y;
};

Tableau.prototype.LUEvaluateBis = function (L, U, N, row, col) {
	var j = 0;
	var n = this.nextBasisIndex;
	var x;
	var y;

	y = N[row + 1][col + 1];
	console.log("y", y);
	for (j = 0; j < row; j++) {
		y -= L[row][j] * N[j + 1][col + 1];
		console.log("tmpy", y, "; y -=", L[row][j], "*", N[j + 1][col + 1]);
	}
	y /= L[row][row];
	console.log("tmpy", y, "; y /=", L[row][row]);

	x = y;
	for (j = row + 1; j < n; j++) {
		x -= U[row][j] * N[j + 1][col + 1];
		console.log("tmpx", x, "; x -=", U[row][j], "*", N[j + 1][col + 1]);
	}
	x /= U[row][row];
	console.log("tmpx", x, "; x /=", U[row][row]);

	return x;
};

// http://best.eng.buffalo.edu/Research/Lecture%20Series%202013/General%20Linear%20Systems.pdf
Tableau.prototype.LUEvaluateBis2 = function (L, U, N, row) {
	var n = this.width - 1;
	var i, j;

	console.log("row 0 =", row[0], "/", L[0][0]);
	row[0] = row[0] / L[0][0];
	console.log("=", row[0]);
	for (i = 1; i < n; i++) {
		for (j = 0; j < i; j++) {
			console.log("row", i, "=", "(", row[i], "-", L[i][j], "*", row[j], ")", "/", L[i][i]);
			// row[i] = (row[i] - L[i][j] * row[j]) / L[i][i];
			row[i] -= L[i][j] * row[j];
			console.log("=", row[i]);
		}
		row[i] /= L[i][i];
	}

	console.log("debug y", JSON.stringify(row));

	console.log("row", n-1, "=", row[n - 1], "/", U[n - 1][n - 1]);
	row[n - 1] = row[n - 1] / U[n - 1][n - 1];
	console.log(row[n - 1]);
	for (i = n - 2; i >= 0; i--) {
		for (j = i + 1; j < n; j++) {
			console.log("row", i, "=", "(", row[i], "-", U[i][j], "*", row[j], ")", "/", U[i][i]);
			// row[i] = (row[i] - U[i][j] * row[j]) / U[i][i];
			row[i] -= U[i][j] * row[j];
			console.log("=", row[i]);
		}
		row[i] /= U[i][i];
	}

	// x[i] = y[i];
	// for (j = i + 1; j < n; j++) {
	// 	x[i] -= U[i][j] * x[j];
	// }
	// x[i] /= U[i][i];

	return row;
};

Tableau.prototype.LUEvaluateBis3 = function (L, U, N, row, index) {
	var n = this.width - 1;
	var i, j;

	console.log("index", index);
	console.log("the row", row);
	console.log("row 0 =", row[0], "/", L[0][0]);
	console.log("=", row[0]);
	for (i = 0; i < n; i++) {
		for (j = 0; j < i; j++) {
			console.log("row", i, "=", "(", row[i], "-", L[i][j], "*", row[j], ")");
			row[i] -= L[i][j] * row[j];
			console.log("=", row[i]);

			// console.log("row", i, "=", "(", row[i], "-", L[j][i], "*", row[j], ")");
			// row[i] -= L[j][i] * row[j];
			// console.log("=", row[i]);
		}
		console.log("row", i, "/=", L[i][i]);
		row[i] /= L[i][i];
		console.log("=", row[i]);

		// console.log("row", i, "/=", L[index][index]);
		// row[i] /= L[index][index];
		// console.log("=", row[i]);
	}

	console.log("debug y", JSON.stringify(row));

	console.log("row", n-1, "=", row[n - 1], "/", U[n - 1][n - 1]);
	console.log(row[n - 1]);
	for (i = n - 1; i >= 0; i--) {
		for (j = i + 1; j < n; j++) {
			// console.log("row", i, "=", "(", row[i], "-", U[i][j], "*", row[j], ")");
			// row[i] -= U[i][j] * row[j];
			// console.log("=", row[i]);

			console.log("row", i, "=", "(", row[i], "-", U[j][i], "*", row[j], ")");
			row[i] -= U[j][i] * row[j];
			console.log("=", row[i]);
		}
		// console.log("row", i, "/=", U[i][i]);
		// row[i] /= U[i][i];
		// console.log("=", row[i]);

		console.log("row", i, "/=", U[index][index]);
		row[i] /= U[index][index];
		console.log("=", row[i]);
	}

	return row;
};

Tableau.prototype.yay = function (L, U, N, row) {
	var width = this.width - 1;
	var result = new Array(width);

	for (var i = 0; i < width; i++) {
		for (var j = 0; j < i; j++) {
			row[i] -= L[i][j] * result[j];
		}
		result[i] = row[i] / L[i][i];
	}

	for (var i = width - 1; i >= 0; i--) {
		for (var j = i + 1; j < width; j++) {
			row[i] -= U[i][j] * result[j];
		}
		result[i] = row[i] / U[i][i];
	}

	return result;
};

Tableau.prototype.LUEvaluateRow = function (L, U, N, r) {
	var height = this.height - 1;
	var width = this.width - 1;
	var col = new Array(height);
	var row = new Array(width);

	console.log(this.displayMatrix(this.basis, "B"));
	console.log(this.displayMatrix(L, "L"));
	console.log(this.displayMatrix(U, "U"));
	console.log(this.displayMatrix(N, "N"));
	// console.log(this.displayMatrix(this.LUEvaluateMatrix(L, U), "evaluated N"));

	for (var i = 0; i < width; i++) {
		for (var j = 0; j < height; j++) {
			col[j] = N[j + 1][i + 1];
		}
		row[i] = this.LUEvaluate(L, U, col)[0][r - 1];
	}

	console.log("\n");
	console.log("TRUE ROW", JSON.stringify(row));

	// var tmpRow = [];
	// for (var i = 0; i < width; i++) {
	// 	tmpRow.push(this.LUEvaluateBis(L, U, N, r - 1, i));
	// }
	// console.log("\n");
	// console.log("GOOD ?", JSON.stringify(tmpRow));




	console.log("\n");
	console.log("NEW ONE");
	var rowww = this.LUEvaluateBis3(L, U, N, N[r].slice(1), r-1);
	console.log(JSON.stringify(rowww));

	console.log("\n");
	console.log("NEW new");
	var yay = this.yay(L, U, N, N[r].slice(1));
	console.log(JSON.stringify(yay));




	console.log("\n\n\n\n\n");
	return row;
	// return rowww;
};

Tableau.prototype.LUEvaluateMatrix = function (L, U) {
	var height = this.height - 1;
	var width = this.width - 1;

	// var dummyRow = Array.from({ length: width }, () => 0);
	var dummyRow = new Array(width);
	dummyRow.fill(0);
	var realMatrix = new Array(height);
	for (var i = 0; i < height; i++) {
		realMatrix[i] = dummyRow.slice();
	}

	for (i = 0; i < width; i++) {
		var col = new Array(height);
		for (var j = 0; j < height; j++) {
			col[j] = this.matrix[j + 1][i + 1];
		}
		var realCol = this.LUEvaluate(L, U, col)[0];
		for (j = 0; j < height; j++) {
			realMatrix[j][i] = realCol[j];
		}
	}

	return realMatrix;
};

function transposeMatrix(M) {
	var width = M.length;
	var height = M[0].length;

	var tmpRow = new Array(width);

	var M_T = new Array(height);
	for (var r = 0; r < height; r++) {
		M_T[r] = tmpRow.slice();
		for (var c = 0; c < width; c++) {
			M_T[r][c] = M[c][r];
		}
	}

	return M_T;
}

function matrixXMatrix(M1, M2) {
	var width = M2[0].length;
	var height = M1.length;

	var tmpRow = new Array(width);
	for (var i = 0; i < width; i++) {
		tmpRow[i] = 0;
	}

	var M = new Array(height);
	for (i = 0; i < height; i++) {
		M[i] = tmpRow.slice();
	}

	for (i = 0; i < M1.length; i++) {
		for (var j = 0; j < M2[0].length; j++) {
			for (var k = 0; k < M2.length; k++) {
				M[i][j] += M1[i][k] * M2[k][j];
			}
		}
	}

	return M;
}

function matrixXVector(M, V) {
	var height = M.length;

	var vect = new Array(height);
	for (var i = 0; i < height; i++) {
		vect[i] = 0;
	}

	for (i = 0; i < height; i++) {
		for (var j = 0; j < M[0].length; j++) {
			vect[i] += M[i][j] * V[j];
		}
	}

	return vect;
}

Tableau.prototype.updateLU = function (B, L, U, b, invLXa_q, pivotIndex) {
	var size = this.nextBasisIndex;
	var i, j;

	// TODO : instead of recomputing LU every time, update them
	// recompute LU
	// TODO : instead of PLU, put it straight into L and U
	// console.log("HERE BEFORE", JSON.stringify(b));
	var PLU = this.decompose2(B, b);
	// console.log("HERE AFTER", JSON.stringify(b));

	var newMat;
	newMat = PLU[1];
	for (i = 0; i < size; i++) {
		for (j = 0; j < size; j++) {
			U[i][j] = newMat[i][j];
		}
	}

	newMat = PLU[0];
	for (i = 0; i < size; i++) {
		for (j = 0; j < size; j++) {
			L[i][j] = newMat[i][j];
		}
	}
};

Array.prototype.extend = function (otherArray) {
	// should include a test to check whether otherArray really is an array ?
	otherArray.forEach(function(v) {this.push(v)}, this);
}

Function.prototype.clone = function() {
	var that = this;
	var temp = function temporary() { return that.apply(this, arguments); };
	for(var key in this) {
		if (this.hasOwnProperty(key)) {
			temp[key] = this[key];
		}
	}
	return temp;
};

Tableau.prototype.LUSimplexPhase1 = function () {
	// setup of the temporary L and U according to the characetristics of the problem/current branch
	if (this.nextBasisIndex > this.tmpL.length) {
		var nextBasisIndex = this.nextBasisIndex;
		var originalLength = this.tmpL.length;
		var tmpL = this.tmpL;
		var tmpU = this.tmpU;
		// TODO : fill not needed ?
		var toAppend = new Array(nextBasisIndex - originalLength).fill(0);
		for (i = originalLength; i < nextBasisIndex; i++) {
			// TODO : fill not needed ?
			tmpL.push(new Array(nextBasisIndex).fill(0));
			tmpU.push(new Array(nextBasisIndex).fill(0));
		}
		for (var i = 0; i < originalLength; i++) {
			tmpL[i].extend(toAppend);
			tmpU[i].extend(toAppend);
		}
	}

    var debugCheckForCycles = this.model.checkForCycles;
    var varIndexesCycle = [];

	var N = this.matrix;
	var B = this.basis;
	var cB = this.basisCosts;
	this.originalZ = 0;
	var originalZ = this.originalZ;
	var nOptionalObjectives = this.optionalObjectives.length;
	var cBOptionals = this.basisOptionalCosts;

	var b = this.originalRHS.slice();
	// console.log("HERE originalRHS", b);

	this.savedLog = console.log.clone();
	console.log = function() {}
	var LU = this.decompose2(B, b);
	var LU_T = this.decompose(transposeMatrix(B));

	this.LU = LU;
	this.LU_T = LU_T;

	var cN = N[0].slice(1);

	var updated_b = this.LUEvaluate(LU[0], LU[1], b)[0];

    var rhsColumn = this.rhsColumn;
    var lastColumn = this.width - 1;
    var lastRow = this.height - 1;

    var unrestricted;
	var precision = this.precision;
    var iterations = 0;

	// this.displayTableau();
	// console.log("real matrix", JSON.stringify(this.LUEvaluateMatrix(LU[0], LU[1])));

    while (true) {
		console.log = this.savedLog.clone();
		console.log("ITERATION PHASE 1", iterations);
		console.log = function() {}


		// if (iterations === 1) {
		// 	throw true;
		// }

		// console.log("rowByVarIndex", JSON.stringify(this.rowByVarIndex));
		// console.log("varIndexByRow", JSON.stringify(this.varIndexByRow));
		// console.log("unrestricted", JSON.stringify(this.unrestrictedVars));

		// console.log("LU[0]", JSON.stringify(LU[0]));
		// console.log("LU[1]", JSON.stringify(LU[1]));
		// console.log("B", JSON.stringify(B));
		var debugLog = false;
		// this.displayTableau();
		// this.debugLog(function () { console.log("updated b", JSON.stringify(updated_b)); }, debugLog);
		// console.log("reverse b ?", this.reverseLUEvaluate(LU[0], LU[1], updated_b));

		// Selecting leaving variable (feasibility condition):
		// Basic variable with most negative value
		var leavingRowIndex = 0;
		var rhsValue = -precision;
		for (var r = 1; r <= lastRow; r++) {
			unrestricted = this.unrestrictedVars[this.varIndexByRow[r]] === true;
			if (unrestricted) {
				continue;
			}

			var value = updated_b[r - 1];
			if (value < rhsValue - precision) {
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

		var u = this.LUEvaluate(LU_T[0], LU_T[1], cB)[0];
		// console.log("u LUEvaluate", JSON.stringify(u));

		var updated_cN = cN.slice();
		var tmpVect = new Array(this.width - 1);
		for (var i = 0; i < tmpVect.length; i++) {
			tmpVect[i] = 0;
		}
		for (i = 0; i < tmpVect.length; i++) {
			for (var j = 0; j < this.height - 1; j++) {
				tmpVect[i] += u[j] * N[j + 1][i + 1];
			}
		}
		// console.log("uUu", JSON.stringify(u));
		// console.log("tmpVect", JSON.stringify(tmpVect));
		for (var rc = 0; rc < this.width - 1; rc++) {
			updated_cN[rc] -= tmpVect[rc];
		}


		// this.displayMatrix(LU[0], "LU[0]");
		// this.displayMatrix(LU[1], "LU[1]");
		// this.displayMatrix(B, "B");


		// Compute the row according to the current basis
		// TODO : optimize
		var leavingRow = this.LUEvaluateRow(LU[0], LU[1], N, leavingRowIndex);
		// this.debugLog(function () { console.log("leaving row", leavingRowIndex, JSON.stringify(leavingRow)); }, debugLog);
		// this.debugLog(function () { console.log("updated_cN", JSON.stringify(updated_cN)); }, debugLog);

		// console.log("leavingRow", JSON.stringify(leavingRow));


		for (var c = 1; c <= lastColumn; c++) {
			var coefficient = leavingRow[c - 1];
			if (-precision < coefficient && coefficient < precision) {
				continue;
			}

			unrestricted = this.unrestrictedVars[this.varIndexByCol[c]] === true;
			if (unrestricted || coefficient < -precision) {
				var quotient = -updated_cN[c - 1] / coefficient;
				if (maxQuotient < quotient - precision) {
					maxQuotient = quotient;
					enteringColumn = c;
				}
			}
		}

		var aq = new Array(this.height - 1);
		for (r = 0; r < aq.length; r++) {
			aq[r] = N[r + 1][enteringColumn];
		}
		// console.log("aq", aq);
		var aqInfo = this.LUEvaluate(LU[0], LU[1], aq);

		// console.log("entering column", JSON.stringify(aqInfo[0]));

		if (enteringColumn === 0) {
			// Not feasible
			this.feasible = false;
			return iterations;
		}

		if (debugCheckForCycles) {
			varIndexesCycle.push([this.varIndexByRow[leavingRowIndex], this.varIndexByCol[enteringColumn]]);

			var cycleData = this.checkForCycles(varIndexesCycle);
			if (cycleData.length > 0) {
				console.log("Cycle in phase 1");
				console.log("Start :", cycleData[0]);
				console.log("Length :", cycleData[1]);
				throw new Error();
			}
		}

		// console.log("b", JSON.stringify(updated_b));

		rhsValue = updated_b[leavingRowIndex - 1];
		var colValue = aqInfo[0][leavingRowIndex - 1];


		// this.debugLog(function () { console.log("updated aq", enteringColumn, JSON.stringify(aqInfo[0])); }, debugLog);
		var minRatio = rhsValue / colValue;

		// if (iterations === 3) {
		// 	this.switchBasicColumns(14, 16);
		// } else if (iterations === 4) {
		// 	this.switchRows(14, 16);
		// }

		console.log = this.savedLog.clone();
		console.log(leavingRowIndex, enteringColumn);
		console.log = function() {}

		this.revisedPivot(leavingRowIndex - 1, enteringColumn - 1, updated_b, cN, LU, LU_T, aqInfo, originalZ, minRatio);
		iterations += 1;

		// this.displayTableau();
		// console.log("real matrix", JSON.stringify(this.LUEvaluateMatrix(LU[0], LU[1])));
		// console.log("b after pivot", JSON.stringify(updated_b));
		// console.log("LU[0]", JSON.stringify(LU[0]));
		// console.log("LU[1]", JSON.stringify(LU[1]));
		// console.log("B", JSON.stringify(B));
	}
};

Tableau.prototype.LUSimplexPhase2 = function () {
	var debugCheckForCycles = this.model.checkForCycles;
	var varIndexesCycle = [];
	var iter = 0;
	var precision = this.precision;
	var i;
	var j;

	var N = this.matrix;

	var originalZ = this.originalZ;

	var B = this.basis;

	var cB = this.basisCosts;

	var nOptionalObjectives = this.optionalObjectives.length;

	var cBOptionals = this.basisOptionalCosts;

	// this.displayTableau();

	var b = this.originalRHS.slice();

	var LU = this.decompose2(B, b);
	var LU_T = this.decompose(transposeMatrix(B));

	this.LU = LU;
	this.LU_T = LU_T;

	var cN = N[0].slice(1);

	var updated_b = this.LUEvaluate(LU[0], LU[1], b)[0];
	// console.log("HERE original rhs", b);

	var reducedCost, unrestricted;

	console.log("START");
	// this.displayTableau();

	while(true) {
		console.log = this.savedLog.clone();
		console.log("ITERATION PHASE 2", iter);
		console.log = function() {}
		// console.log("rowByVarIndex", JSON.stringify(this.rowByVarIndex));
		// console.log("varIndexByRow", JSON.stringify(this.varIndexByRow));
		// console.log("unrestricted", JSON.stringify(this.unrestrictedVars));
		var debugLog = false;
		// if (debugLog) {
		// this.displayMatrix(this.LUEvaluateMatrix(LU[0], LU[1]), "MATRIX");
		// }

		var optionalCostsColumns = null;
		if (nOptionalObjectives > 0) {
			optionalCostsColumns = [];
		}

		// this.displayMatrix(LU[0], "LU[0]");
		// this.displayMatrix(LU[1], "LU[1]");
		// this.displayMatrix(B, "B");

		// console.log("LU[0]", JSON.stringify(LU[0]));
		// console.log("LU[1]", JSON.stringify(LU[1]));
		// console.log("B", JSON.stringify(B));

		var u = this.LUEvaluate(LU_T[0], LU_T[1], cB)[0];

		var updated_cN = cN.slice();
		var tmpVect = new Array(this.width - 1);
		for (i = 0; i < tmpVect.length; i++) {
			tmpVect[i] = 0;
		}
		for (i = 0; i < tmpVect.length; i++) {
			for (j = 0; j < u.length; j++) {
				tmpVect[i] += u[j] * N[j + 1][i + 1];
			}
		}
		for (var rc = 0; rc < this.width - 1; rc++) {
			updated_cN[rc] -= tmpVect[rc];
		}
		// this.debugLog(function () { console.log("cB", JSON.stringify(cB)); }, debugLog);
		// this.debugLog(function () { console.log("updated_cN", JSON.stringify(updated_cN)); }, debugLog);
		// this.debugLog(function () { console.log("b", JSON.stringify(updated_b)); }, debugLog);


		var isReducedCostNegative = false;
		var enteringValue = precision;
		var enteringColumn =  -1;

		for (var c = 0; c < this.width - 1; c++) {
			reducedCost = updated_cN[c];
			unrestricted = this.unrestrictedVars[this.varIndexByCol[c + 1]] === true;

			if (nOptionalObjectives > 0 && -precision < reducedCost && reducedCost < precision) {
				optionalCostsColumns.push(c);
				continue;
			}

			if (unrestricted && reducedCost < 0) {
				if (-reducedCost > enteringValue + precision) {
					enteringValue = -reducedCost;
					enteringColumn = c;
					isReducedCostNegative = true;
				}
				continue;
			}

			if (reducedCost > enteringValue + precision) {
				enteringValue = reducedCost;
				enteringColumn = c;
				isReducedCostNegative = false;
			}
		}

		var tmp_cN, uOptional;
		if (nOptionalObjectives > 0) {
			if (debugLog) {
				for (var k = 0; k < nOptionalObjectives; k++) {
					tmp_cN = this.optionalObjectives[k].reducedCosts.slice(1);
					uOptional = this.LUEvaluate(LU_T[0], LU_T[1], this.basisOptionalCosts[k])[0];
					for (i = 0; i < tmpVect.length; i++) {
						tmpVect[i] = 0;
					}
					for (i = 0; i < tmpVect.length; i++) {
						for (j = 0; j < uOptional.length; j++) {
							tmpVect[i] += uOptional[j] * N[j + 1][i + 1];
						}
					}
					for (rc = 0; rc < this.width - 1; rc++) {
						tmp_cN[rc] -= tmpVect[rc];
					}
					// console.log("optional", k, [this.optionalObjectives[k].reducedCosts[0]], tmp_cN);
				}
			}

			var o = 0;

			while(enteringColumn === -1 && optionalCostsColumns.length > 0 && o < nOptionalObjectives) {
				var optionalCostsColumns2 = [];
				tmp_cN = this.optionalObjectives[o].reducedCosts.slice(1);
				uOptional = this.LUEvaluate(LU_T[0], LU_T[1], this.basisOptionalCosts[o])[0];
				for (i = 0; i < tmpVect.length; i++) {
					tmpVect[i] = 0;
				}
				for (i = 0; i < tmpVect.length; i++) {
					for (j = 0; j < uOptional.length; j++) {
						tmpVect[i] += uOptional[j] * N[j + 1][i + 1];
					}
				}
				for (rc = 0; rc < this.width - 1; rc++) {
					tmp_cN[rc] -= tmpVect[rc];
				}

				enteringValue = precision;

				var tmpCost;
				for (i = 0; i < optionalCostsColumns.length; i++) {
					c = optionalCostsColumns[i];
					tmpCost = tmp_cN[c];
					unrestricted = this.unrestrictedVars[this.varIndexByCol[c + 1]] === true;

					if (-precision < tmpCost && tmpCost < precision) {
						// console.log("HERE skip a");
						optionalCostsColumns2.push(c);
						continue;
					}

					if (unrestricted && tmpCost < 0) {
						// if (-tmpCost > enteringValue) {
						if (-tmpCost > enteringValue + precision) {
							// console.log("HERE unrestricted and tmpcost", tmpCost);
							enteringValue = -tmpCost;
							enteringColumn = c;
							isReducedCostNegative = true;
						}
						continue;
					}

					// if (tmpCost > enteringValue) {
					if (tmpCost > enteringValue + precision) {
						// console.log("HERE tmpcost only", tmpCost);
						enteringValue = tmpCost;
						enteringColumn = c;
						isReducedCostNegative = false;
					}
				}
				optionalCostsColumns = optionalCostsColumns2;
				o++;
			}
		}

		if (enteringColumn ===  -1) {
			// console.log(JSON.stringify(this.varIndexByRow));
			// console.log(JSON.stringify(this.rowByVarIndex));
			for (i = 1; i < this.height; i++) {
				N[i][0] = updated_b[i - 1];
			}
			this.setEvaluation();
			return iter;
		}

		var aq = new Array(this.height - 1);
		for (var r = 0; r < aq.length; r++) {
			aq[r] = N[r + 1][enteringColumn + 1];
		}
		// console.log("aq", JSON.stringify(aq));
		var aqInfo = this.LUEvaluate(LU[0], LU[1], aq);
		var updated_aq = aqInfo[0];
		var invLXa_q = aqInfo[1];
		// this.debugLog(function () { console.log("updated_aq", enteringColumn + 1, ":", JSON.stringify(updated_aq)); }, debugLog);



		var minQuotient = Infinity;
		var leavingRow = -1;

		for (r = 0; r < updated_b.length; r++) {
			// console.log("minQuotient", minQuotient);
			var rhsValue = updated_b[r];
			var colValue = updated_aq[r];

			if (-precision < colValue && colValue < precision) {
				continue;
			}

			if (colValue > 0 && precision > rhsValue && rhsValue > -precision) {
				minQuotient = 0;
				leavingRow = r;
				break;
			}

			var quotient = isReducedCostNegative ? -rhsValue / colValue : rhsValue / colValue;
			if (quotient > precision && minQuotient > quotient + precision) {
				minQuotient = quotient;
				leavingRow = r;
			}
		}
		minQuotient = isReducedCostNegative ? -minQuotient : minQuotient;
		// console.log("minQuotient", minQuotient);

		var tmpLeavingRow = this.LUEvaluateRow(LU[0], LU[1], N, leavingRow);
		// this.debugLog(function () { console.log("HERE leaving row", leavingRow + 1, ":", tmpLeavingRow); }, debugLog);


		if (minQuotient === Infinity) {
			// optimal value is -Infinity
			this.evaluation = -Infinity;
			this.bounded = false;
			this.unboundedVarIndex = this.varIndexByCol[enteringColumn + 1];
			return iter;
		}

		if (debugCheckForCycles) {
			varIndexesCycle.push([this.varIndexByRow[leavingRow + 1], this.varIndexByCol[enteringColumn + 1]]);

			var cycleData = this.checkForCycles(varIndexesCycle);
			if (cycleData.length > 0) {
				console.log("Cycle in phase 2");
				console.log("Start :", cycleData[0]);
				console.log("Length :", cycleData[1]);
				throw new Error();
			}
		}

		console.log = this.savedLog.clone();
		console.log(leavingRow + 1, enteringColumn + 1);
		console.log = function() {}
		this.revisedPivot(leavingRow, enteringColumn, updated_b, cN, LU, LU_T, aqInfo, originalZ, minQuotient);

		iter++;

		// this.displayTableau();
		// console.log("real matrix", JSON.stringify(this.LUEvaluateMatrix(LU[0], LU[1])));
		// console.log("b after pivot", JSON.stringify(updated_b));
		// console.log("LU[0]", JSON.stringify(LU[0]));
		// console.log("LU[1]", JSON.stringify(LU[1]));
		// console.log("B", JSON.stringify(B));

		// this.displayTableau();

		// // console.log("BIdx", BIdx);
		// console.log("B", JSON.stringify(B));
		// console.log("new cB", JSON.stringify(cB));
		// // console.log("NIdx", NIdx);
		// console.log("N", JSON.stringify(N));
		// console.log("new cN", JSON.stringify(cN));
		// console.log("updated_b", JSON.stringify(updated_b));
		// console.log("z =", z);
		// console.log("\n\n");

		// if (iter === 3) {
		// throw new Error();
		// }
	}
};

Tableau.prototype.revisedPivot = function (leavingRow, enteringColumn, b, cN, LU, LU_T, aqInfo, originalZ, minQuotient) {
	var updated_aq = aqInfo[0];
	var invLXa_q = aqInfo[1];
	var N = this.matrix;
	var B = this.basis;
	var cB = this.basisCosts;
	var cBOptionals = this.basisOptionalCosts;
	var i, j, r;
	var size = this.nextBasisIndex;

	for (r = 0; r < b.length; r++) {
		// console.log("HERE b_"+r+" =", b[r], "-", minQuotient, "*", updated_aq[r], "===");
		b[r] -= minQuotient * updated_aq[r];
		// console.log(b[r]);
		N[r + 1][0] = b[r];
		// console.log("HERE diff_"+r, minQuotient * updated_aq[r]);
	}
	// console.log("HERE b_"+leavingRow+" =", minQuotient);
	b[leavingRow] = minQuotient;
	N[leavingRow + 1][0] = b[leavingRow];

	var leavingBasicIndex = this.varIndexByRow[leavingRow + 1];
	var enteringBasicIndex = this.varIndexByCol[enteringColumn + 1];

	this.varIndexByRow[leavingRow + 1] = enteringBasicIndex;
	this.varIndexByCol[enteringColumn + 1] = leavingBasicIndex;

	this.rowByVarIndex[enteringBasicIndex] = leavingRow + 1;
	this.rowByVarIndex[leavingBasicIndex] = -1;

	this.colByVarIndex[enteringBasicIndex] = -1;
	this.colByVarIndex[leavingBasicIndex] = enteringColumn + 1;

	var pivot = N[leavingRow + 1][enteringColumn + 1];

	// Update B and N
	for (r = 0; r < size; r++) {
		var tmpVal = B[r][leavingRow];

		B[r][leavingRow] = N[r + 1][enteringColumn + 1];

		N[r + 1][enteringColumn + 1] = tmpVal;
	}
	N[0][enteringColumn + 1] = cB[leavingRow];

	var tmp_cNCost = cN[enteringColumn];
	cN[enteringColumn] = cB[leavingRow];
	cB[leavingRow] = tmp_cNCost;

	if (this.optionalObjectives.length > 0) {
		for (i = 0; i < cBOptionals.length; i++) {
			tmp_cNCost = this.optionalObjectives[i].reducedCosts[enteringColumn + 1];
			this.optionalObjectives[i].reducedCosts[enteringColumn + 1] = cBOptionals[i][leavingRow];
			cBOptionals[i][leavingRow] = tmp_cNCost;
		}
	}

	var z = 0;
	for (i = 0; i < size; i++) {
		z += b[i] * cB[i];
	}
	N[0][0] = -(z - originalZ);

	if (cBOptionals) {
		for (i = 0; i < cBOptionals.length; i++) {
			z = 0;
			var optionalCB = cBOptionals[i];
			var optionalCN = this.optionalObjectives[i].reducedCosts;
			for (j = 0; j < size; j++) {
				z += b[j] * optionalCB[j];
			}
			optionalCN[0] = -z;
		}
	}

	this.updateLU(B, LU[0], LU[1], b, invLXa_q, leavingRow);
	var tmpM = this.decompose(transposeMatrix(B));

	// TODO : optimize (update from previous transpose, full transpose not necessary)
	var newMat = tmpM[0];
	for (i = 0; i < size; i++) {
		for (j = 0; j < size; j++) {
			LU_T[0][i][j] = newMat[i][j];
		}
	}

	newMat = tmpM[1];
	for (i = 0; i < size; i++) {
		for (j = 0; j < size; j++) {
			LU_T[1][i][j] = newMat[i][j];
		}
	}
};

Tableau.prototype._revisedPutInBase = function (varIndex) {
	// Same logic as in _putInBase
	var r = this.rowByVarIndex[varIndex];
	if (r ===  - 1) {
		var basis = this.basis;
		var matrix = this.matrix;
		var tmpVal;
		var nextBasisIndex = this.nextBasisIndex;
		// Outside the base
		// pivoting to take it out
		var c = this.colByVarIndex[varIndex];

		// Selecting pivot row
		// (Any row with coefficient different from 0)
		for (var r1 = 1; r1 < this.height; r1 += 1) {
			var coefficient = this.matrix[r1][c];
			if (coefficient < -this.precision || this.precision < coefficient) {
				r = r1;
				break;
			}
		}

		// switch columns
		for (var i = 0; i < nextBasisIndex; i++) {
			tmpVal = basis[i][r - 1];
			basis[i][r - 1] = matrix[i + 1][c];
			matrix[i + 1][c] = tmpVal;
		}

		// switch costs
		tmpVal = this.basisCosts[r - 1];
		this.basisCosts[r - 1] = matrix[0][c];
		matrix[0][c] = tmpVal;

		// switch optional costs
		var basisOptionalCosts = this.basisOptionalCosts;
		if (basisOptionalCosts !== null) {
			var optionalObjectives = this.optionalObjectives;
			for (i = 0; i < basisOptionalCosts.length; i++) {
				tmpVal = basisOptionalCosts[i][r - 1];
				basisOptionalCosts[i][r - 1] = this.optionalObjectives[i].reducedCosts[c];
				this.optionalObjectives[i].reducedCosts[c] = tmpVal;
			}
		}


		// switch indexes between varIndexByRow/col and row/colByVarIndex
		var leavingBasicIndex = this.varIndexByRow[r];
		var enteringBasicIndex = this.varIndexByCol[c];

		this.varIndexByRow[r] = enteringBasicIndex;
		this.varIndexByCol[c] = leavingBasicIndex;

		this.rowByVarIndex[enteringBasicIndex] = r;
		this.rowByVarIndex[leavingBasicIndex] = -1;

		this.colByVarIndex[enteringBasicIndex] = -1;
		this.colByVarIndex[leavingBasicIndex] = c;
	}
	return r;
};

Tableau.prototype._revisedTakeOutOfBase = function (varIndex) {
	var c = this.colByVarIndex[varIndex];
	var matrix = this.matrix;
	if (c ===  - 1) {
		// Same logic as in _takeOutOfBase
		// select entering variable to switch with
		var r = this.rowByVarIndex[varIndex];
		var pivotRow = matrix[r];
		for (var c1 = 1; c1 < this.height; c1 += 1) {
			var coefficient = pivotRow[c1];
			if (coefficient < -this.precision || this.precision < coefficient) {
				c = c1;
				break;
			}
		}

		// switch columns
		var basis = this.basis;
		var nextBasisIndex = this.nextBasisIndex;
		for (var i = 0; i < nextBasisIndex; i++) {
			var tmpVal = basis[i][r - 1];
			basis[i][r - 1] = matrix[i + 1][c];
			matrix[i + 1][c] = tmpVal;
		}

		// switch between varIndexByRow/col and row/colByVarIndex
		var leavingBasicIndex = this.varIndexByRow[r];
		var enteringBasicIndex = this.varIndexByCol[c];

		this.varIndexByRow[r] = enteringBasicIndex;
		this.varIndexByCol[c] = leavingBasicIndex;

		this.rowByVarIndex[enteringBasicIndex] = r;
		this.rowByVarIndex[leavingBasicIndex] = -1;

		this.colByVarIndex[enteringBasicIndex] = -1;
		this.colByVarIndex[leavingBasicIndex] = c;
	}
	return c;
};

// Used for the permutation process (in case a basis is not decomposable)
Tableau.prototype._exchangeBasicVariables = function (row1, row2) {
	// TODO : test if both are basic
	// TODO : test if revised method is used
	var B = this.basis;
	var N = this.matrix;
	var tmp;
	var i;

	for (i = 0; i < this.height - 1; i++) {
		tmp = B[i][row1 - 1];
		B[i][row1 - 1] = B[i][row2 - 1];
		B[i][row2 - 1] = tmp;
	}
	for (i = 0; i < this.height - 1; i++) {
		tmp = B[row1 - 1][i];
		B[row1 - 1][i] = B[row2 - 1][i];
		B[row2 - 1][i] = tmp;
	}
	for (i = 0; i < this.width; i++) {
		// console.log(N);
		tmp = N[row1][i];
		N[row1][i] = N[row2][i];
		N[row2][i] = tmp;
	}

	var basicIndex1 = this.varIndexByRow[row1];
	var basicIndex2 = this.varIndexByRow[row2];

	this.varIndexByRow[row1] = basicIndex2;
	this.varIndexByRow[row2] = basicIndex1;

	this.rowByVarIndex[basicIndex1] = row2;
	this.rowByVarIndex[basicIndex2] = row1;

	tmp = this.basisCosts[row1 - 1];
	this.basisCosts[row1 - 1] = this.basisCosts[row2 - 1];
	this.basisCosts[row2 - 1] = tmp;

	var basisOptionalCosts = this.basisOptionalCosts;
	if (basisOptionalCosts !== null) {
		for (i = 0; i < basisOptionalCosts.length; i++) {
			tmp = basisOptionalCosts[row1 - 1];
			basisOptionalCosts[row1 - 1] = basisOptionalCosts[row2 - 1];
			basisOptionalCosts[row2 - 1] = tmp;
		}
	}

	tmp = this.originalRHS[row1 - 1];
	this.originalRHS[row1 - 1] = this.originalRHS[row2 - 1];
	this.originalRHS[row2 - 1] = tmp;
};


Tableau.prototype.switchRows = function (row1, row2) {
	if (row1 !== row2) {
		// console.log("before switching rows", JSON.stringify(this.LUEvaluateMatrix(this.LU[0], this.LU[1])));
		// console.log("switching rows !", row1, row2);
		var i, tmp;
		var N = this.matrix;
		var B = this.basis;
		for (i = 0; i < this.height - 1; i++) {
			tmp = B[row1 - 1][i];
			B[row1 - 1][i] = B[row2 - 1][i];
			B[row2 - 1][i] = tmp;
		}
		// for (i = 0; i < this.height - 1; i++) {
		// 	tmp = B[i][row1 - 1];
		// 	B[i][row1 - 1] = B[i][row2 - 1];
		// 	B[i][row2 - 1] = tmp;
		// }
		for (i = 0; i < this.width; i++) {
			tmp = N[row1][i];
			N[row1][i] = N[row2][i];
			N[row2][i] = tmp;
		}

		var basicIndex1 = this.varIndexByRow[row1];
		var basicIndex2 = this.varIndexByRow[row2];

		// this.varIndexByRow[row1] = basicIndex2;
		// this.varIndexByRow[row2] = basicIndex1;
		//
		// this.rowByVarIndex[basicIndex1] = row2;
		// this.rowByVarIndex[basicIndex2] = row1;
		//
		// tmp = this.variablesPerIndex[row1 - 1];
		// this.variablesPerIndex[row1 - 1] = this.variablesPerIndex[row2 - 1];
		// this.variablesPerIndex[row2 - 1] = tmp;

		tmp = this.originalRHS[row1 - 1];
		this.originalRHS[row1 - 1] = this.originalRHS[row2 - 1];
		this.originalRHS[row2 - 1] = tmp;
	}
};

Tableau.prototype.switchBasicColumns = function (col1, col2) {
	if (col1 !== col2) {
		// console.log("switching columns !", col1, col2);
		var tmp;

		// switching in basis
		var B = this.basis;
		for (var i = 0; i < this.nextBasisIndex; i++) {
			tmp = B[i][col1 - 1];
			B[i][col1 - 1] = B[i][col2 - 1];
			B[i][col2 - 1] = tmp;
		}

		// switching in main basis objective
		tmp = this.basisCosts[col1 - 1];
		this.basisCosts[col1 - 1] = this.basisCosts[col2 - 1];
		this.basisCosts[col2 - 1] = tmp;

		// switching in optional basis objectives
		if (this.basisOptionalCosts) {
			for (var i = 0; i < this.basisOptionalCosts.length; i++) {
				tmp = this.basisOptionalCosts[i][col1 - 1];
				this.basisOptionalCosts[i][col1 - 1] = this.basisOptionalCosts[i][col2 - 1];
				this.basisOptionalCosts[i][col2 - 1] = tmp;
			}
		}



		var basicIndex1 = this.varIndexByRow[col1];
		var basicIndex2 = this.varIndexByRow[col2];

		this.varIndexByRow[col1] = basicIndex2;
		this.varIndexByRow[col2] = basicIndex1;

		this.rowByVarIndex[basicIndex1] = col2;
		this.rowByVarIndex[basicIndex2] = col1;

		tmp = this.variablesPerIndex[col1 - 1];
		this.variablesPerIndex[col1 - 1] = this.variablesPerIndex[col2 - 1];
		this.variablesPerIndex[col2 - 1] = tmp;

		// tmp = this.originalRHS[col1 - 1];
		// this.originalRHS[col1 - 1] = this.originalRHS[col2 - 1];
		// this.originalRHS[col2 - 1] = tmp;
	}
}
