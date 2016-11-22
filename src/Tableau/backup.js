/*global require*/
/*global console*/
var Tableau = require("./Tableau.js");

Tableau.prototype.copy = function () {
    var copy = new Tableau(this.precision);

    copy.width = this.width;
    copy.height = this.height;

    copy.nVars = this.nVars;
    copy.model = this.model;

    // Making a shallow copy of integer variable indexes
    // and variable ids
    copy.variables = this.variables;
    copy.variablesPerIndex = this.variablesPerIndex;
    copy.unrestrictedVars = this.unrestrictedVars;
    copy.lastElementIndex = this.lastElementIndex;

    // All the other arrays are deep copied
    copy.varIndexByRow = this.varIndexByRow.slice();
    copy.varIndexByCol = this.varIndexByCol.slice();

    copy.rowByVarIndex = this.rowByVarIndex.slice();
    copy.colByVarIndex = this.colByVarIndex.slice();

    copy.availableIndexes = this.availableIndexes.slice();

    var optionalObjectivesCopy = [];
    for(var o = 0; o < this.optionalObjectives.length; o++){
        optionalObjectivesCopy[o] = this.optionalObjectives[o].copy();
    }
    copy.optionalObjectives = optionalObjectivesCopy;


    var matrix = this.matrix;
    var matrixCopy = new Array(this.height);
    for (var r = 0; r < this.height; r++) {
        matrixCopy[r] = matrix[r].slice();
    }

    copy.matrix = matrixCopy;


    if(this.model.useRevisedSimplex){
        var basis = this.basis;
        var basisCopy = new Array(this.height - 1);
        var nextBasisIndex = this.nextBasisIndex;
        copy.nextBasisIndex = nextBasisIndex;
        for (r = 0; r < nextBasisIndex; r++) {
            basisCopy[r] = basis[r].slice();
        }

        copy.basis = basisCopy;


        copy.basisCosts = this.basisCosts.slice();

        copy.originalRHS = this.originalRHS.slice();


        var basisOptionalCosts = this.basisOptionalCosts;

        if(basisOptionalCosts !== null){
            var basisOptionalCostsCopy = new Array(basisOptionalCosts.length);
            for(o = 0; o < basisOptionalCosts.length; o++){
                basisOptionalCostsCopy[o] = basisOptionalCosts[o].slice();
            }
            copy.basisOptionalCosts = basisOptionalCostsCopy;
        }
    }

    return copy;
};

Tableau.prototype.save = function () {
    this.savedState = this.copy();
};

Tableau.prototype.restore = function () {
    if (this.savedState === null) {
        return;
    }

    var save = this.savedState;
    var savedMatrix = save.matrix;
    this.nVars = save.nVars;
    this.model = save.model;

    // Shallow restore
    this.variables = save.variables;
    this.variablesPerIndex = save.variablesPerIndex;
    this.unrestrictedVars = save.unrestrictedVars;
    this.lastElementIndex = save.lastElementIndex;

    this.width = save.width;
    this.height = save.height;

    // Restoring matrix
    var savedRow;
    var row;
    var r, c;
    for (r = 0; r < this.height; r += 1) {
        savedRow = savedMatrix[r];
        row = this.matrix[r];
        for (c = 0; c < this.width; c += 1) {
            row[c] = savedRow[c];
        }
    }


    // Restoring all the other structures
    var savedBasicIndexes = save.varIndexByRow;
    for (c = 0; c < this.height; c += 1) {
        this.varIndexByRow[c] = savedBasicIndexes[c];
    }

    while (this.varIndexByRow.length > this.height) {
        this.varIndexByRow.pop();
    }

    var savedNonBasicIndexes = save.varIndexByCol;
    for (r = 0; r < this.width; r += 1) {
        this.varIndexByCol[r] = savedNonBasicIndexes[r];
    }

    while (this.varIndexByCol.length > this.width) {
        this.varIndexByCol.pop();
    }

    var savedRows = save.rowByVarIndex;
    var savedCols = save.colByVarIndex;
    for (var v = 0; v < this.nVars; v += 1) {
        this.rowByVarIndex[v] = savedRows[v];
        this.colByVarIndex[v] = savedCols[v];
    }


    if (save.optionalObjectives.length > 0 && this.optionalObjectives.length > 0) {
        this.optionalObjectives = [];
        this.optionalObjectivePerPriority = {};
        for(var o = 0; o < save.optionalObjectives.length; o++){
            var optionalObjectiveCopy = save.optionalObjectives[o].copy();
            this.optionalObjectives[o] = optionalObjectiveCopy;
            this.optionalObjectivePerPriority[optionalObjectiveCopy.priority] = optionalObjectiveCopy;
        }
    }


    if(this.model.useRevisedSimplex){
        // Restoring basis
        var savedBasis = save.basis;
        var basis = this.basis;
        this.nextBasisIndex = save.nextBasisIndex;
        var height = this.nextBasisIndex;
        for(r = 0; r < height; r += 1){
            savedRow = savedBasis[r];
            row = basis[r];
            for(c = 0; c < height; c += 1){
                row[c] = savedRow[c];
            }
        }


        var savedBasisCosts = save.basisCosts;
        var basisCosts = this.basisCosts;
        for(c = 0; c < height; c += 1){
            basisCosts[c] = savedBasisCosts[c];
        }

        for (var i = 0; i < save.nextBasisIndex; i++) {
            this.originalRHS[i] = save.originalRHS[i];
        }


        var savedBasisOptionalCosts = save.basisOptionalCosts;
        if(savedBasisOptionalCosts !== null){
            var nOptionalObjectives = this.optionalObjectives.length;
            var basisOptionalCosts = this.basisOptionalCosts;
            for(r = 0; r < nOptionalObjectives; r += 1){
                basisOptionalCosts[r] = savedBasisOptionalCosts[r].slice();
            }
        }
    }
};
