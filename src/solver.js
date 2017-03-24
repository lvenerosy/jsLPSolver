(function(){if (typeof exports === "object") {module.exports =  require("./main");}})();
(function e(t,n,r){function s(o,u){if(!n[o]){if(!t[o]){var a=typeof require=="function"&&require;if(!u&&a)return a(o,!0);if(i)return i(o,!0);var f=new Error("Cannot find module '"+o+"'");throw f.code="MODULE_NOT_FOUND",f}var l=n[o]={exports:{}};t[o][0].call(l.exports,function(e){var n=t[o][1][e];return s(n?n:e)},l,l.exports,e,t,n,r)}return n[o].exports}var i=typeof require=="function"&&require;for(var o=0;o<r.length;o++)s(r[o]);return s})({1:[function(require,module,exports){
/*global describe*/
/*global require*/
/*global module*/
/*global it*/
/*global console*/
/*global process*/

var Tableau = require("./Tableau/Tableau.js");
var branchAndCut = require("./Tableau/branchAndCut.js");
var expressions = require("./expressions.js");
var Constraint = expressions.Constraint;
var Equality = expressions.Equality;
var Variable = expressions.Variable;
var IntegerVariable = expressions.IntegerVariable;
var Term = expressions.Term;

/*************************************************************
 * Class: Model
 * Description: Holds the model of a linear optimisation problem
 **************************************************************/
function Model(precision, name) {
    this.tableau = new Tableau(precision);

    this.name = name;

    this.variables = [];

    this.integerVariables = [];

    this.unrestrictedVariables = {};

    this.constraints = [];

    this.nConstraints = 0;

    this.nVariables = 0;

    this.isMinimization = true;

    this.tableauInitialized = false;
    this.relaxationIndex = 1;

    this.useRevisedSimplex = false;

    this.useMIRCuts = false;

    this.checkForCycles = false;
}
module.exports = Model;

Model.prototype.minimize = function () {
    this.isMinimization = true;
    return this;
};

Model.prototype.maximize = function () {
    this.isMinimization = false;
    return this;
};

// Model.prototype.addConstraint = function (constraint) {
//     // TODO: make sure that the constraint does not belong do another model
//     // and make
//     this.constraints.push(constraint);
//     return this;
// };

Model.prototype._getNewElementIndex = function () {
    if (this.availableIndexes.length > 0) {
        return this.availableIndexes.pop();
    }

    var index = this.lastElementIndex;
    this.lastElementIndex += 1;
    return index;
};

Model.prototype._addConstraint = function (constraint) {
    var slackVariable = constraint.slack;
    this.tableau.variablesPerIndex[slackVariable.index] = slackVariable;
    this.constraints.push(constraint);
    this.nConstraints += 1;

    if (this.tableauInitialized === true) {
        this.tableau.addConstraint(constraint);
    }

    if(this.useRevisedSimplex){
        var basis = this.tableau.basis;
        var nextBasisIndex = this.tableau.nextBasisIndex;

        var allocate = basis[nextBasisIndex];
        if(allocate === undefined){
            basis.push(new Array(nextBasisIndex + 1));
        }
        var row = basis[nextBasisIndex];
        for(var c = 0; c < nextBasisIndex; c++){
            row[c] = 0;
            if(allocate === undefined){
                basis[c].push(0);
            }
            else{
                basis[c][nextBasisIndex] = 0;
            }
        }
        row[nextBasisIndex] = 1;

        this.tableau.nextBasisIndex++;

        this.tableau.basisCosts.push(0);

        var sign = constraint.isUpperBound ? 1 : -1;
        this.tableau.originalRHS.push(sign * constraint.rhs);


        /*************
            TODO
        **************/
        // update optional basis costs too
    }
};

Model.prototype.smallerThan = function (rhs) {
    var constraint = new Constraint(rhs, true, this.tableau.getNewElementIndex(), this);
    this._addConstraint(constraint);
    return constraint;
};

Model.prototype.greaterThan = function (rhs) {
    var constraint = new Constraint(rhs, false, this.tableau.getNewElementIndex(), this);
    this._addConstraint(constraint);
    return constraint;
};

Model.prototype.equal = function (rhs) {
    var constraintUpper = new Constraint(rhs, true, this.tableau.getNewElementIndex(), this);
    this._addConstraint(constraintUpper);

    var constraintLower = new Constraint(rhs, false, this.tableau.getNewElementIndex(), this);
    this._addConstraint(constraintLower);

    return new Equality(constraintUpper, constraintLower);
};

Model.prototype.addVariable = function (cost, id, isInteger, isUnrestricted, priority) {
    if (typeof priority === "string") {
        switch (priority) {
        case "required":
            priority = 0;
            break;
        case "strong":
            priority = 1;
            break;
        case "medium":
            priority = 2;
            break;
        case "weak":
            priority = 3;
            break;
        default:
            priority = 0;
            break;
        }
    }

    var varIndex = this.tableau.getNewElementIndex();
    if (id === null || id === undefined) {
        id = "v" + varIndex;
    }

    if (cost === null || cost === undefined) {
        cost = 0;
    }

    if (priority === null || priority === undefined) {
        priority = 0;
    }

    var variable;
    if (isInteger) {
        variable = new IntegerVariable(id, cost, varIndex, priority);
        this.integerVariables.push(variable);
    } else {
        variable = new Variable(id, cost, varIndex, priority);
    }

    this.variables.push(variable);
    this.tableau.variablesPerIndex[varIndex] = variable;

    if (isUnrestricted) {
        this.unrestrictedVariables[varIndex] = true;
    }

    this.nVariables += 1;

    if (this.tableauInitialized === true) {
        this.tableau.addVariable(variable);
    }

    return variable;
};

Model.prototype._removeConstraint = function (constraint) {
    var idx = this.constraints.indexOf(constraint);
    if (idx === -1) {
        console.warn("[Model.removeConstraint] Constraint not present in model");
        return;
    }

    this.constraints.splice(idx, 1);
    this.nConstraints -= 1;

    if (this.tableauInitialized === true) {
        this.tableau.removeConstraint(constraint);
    }

    if (constraint.relaxation) {
        this.removeVariable(constraint.relaxation);
    }
};

//-------------------------------------------------------------------
// For dynamic model modification
//-------------------------------------------------------------------
Model.prototype.removeConstraint = function (constraint) {
    if (constraint.isEquality) {
        this._removeConstraint(constraint.upperBound);
        this._removeConstraint(constraint.lowerBound);
    } else {
        this._removeConstraint(constraint);
    }

    return this;
};

Model.prototype.removeVariable = function (variable) {
    var idx = this.variables.indexOf(variable);
    if (idx === -1) {
        console.warn("[Model.removeVariable] Variable not present in model");
        return;
    }
    this.variables.splice(idx, 1);

    if (this.tableauInitialized === true) {
        this.tableau.removeVariable(variable);
    }

    return this;
};

Model.prototype.updateRightHandSide = function (constraint, difference) {
    if (this.tableauInitialized === true) {
        this.tableau.updateRightHandSide(constraint, difference);
    }
    return this;
};

Model.prototype.updateConstraintCoefficient = function (constraint, variable, difference) {
    if (this.tableauInitialized === true) {
        this.tableau.updateConstraintCoefficient(constraint, variable, difference);
    }
    return this;
};


Model.prototype.setCost = function (cost, variable) {
    var difference = cost - variable.cost;
    if (this.isMinimization === false) {
        difference = -difference;
    }

    variable.cost = cost;
    this.tableau.updateCost(variable, difference);
    return this;
};

//-------------------------------------------------------------------
//-------------------------------------------------------------------
Model.prototype.loadJson = function (jsonModel) {
    this.isMinimization = (jsonModel.opType !== "max");

    var variables = jsonModel.variables;
    var constraints = jsonModel.constraints;

    var constraintsMin = {};
    var constraintsMax = {};

    // Instantiating constraints
    var constraintIds = Object.keys(constraints);
    var nConstraintIds = constraintIds.length;

    for (var c = 0; c < nConstraintIds; c += 1) {
        var constraintId = constraintIds[c];
        var constraint = constraints[constraintId];
        var equal = constraint.equal;

        var weight = constraint.weight;
        var priority = constraint.priority;
        var relaxed = weight !== undefined || priority !== undefined;

        var lowerBound, upperBound;
        if (equal === undefined) {
            var min = constraint.min;
            if (min !== undefined) {
                lowerBound = this.greaterThan(min);
                constraintsMin[constraintId] = lowerBound;
                if (relaxed) { lowerBound.relax(weight, priority); }
            }

            var max = constraint.max;
            if (max !== undefined) {
                upperBound = this.smallerThan(max);
                constraintsMax[constraintId] = upperBound;
                if (relaxed) { upperBound.relax(weight, priority); }
            }
        } else {
            lowerBound = this.greaterThan(equal);
            constraintsMin[constraintId] = lowerBound;

            upperBound = this.smallerThan(equal);
            constraintsMax[constraintId] = upperBound;

            var equality = new Equality(lowerBound, upperBound);
            if (relaxed) { equality.relax(weight, priority); }
        }
    }

    var variableIds = Object.keys(variables);
    var nVariables = variableIds.length;

    var integerVarIds = jsonModel.ints || {};
    var binaryVarIds = jsonModel.binaries || {};
    var unrestrictedVarIds = jsonModel.unrestricted || {};

    // Instantiating variables and constraint terms
    var objectiveName = jsonModel.optimize;
    for (var v = 0; v < nVariables; v += 1) {
        // Creation of the variables
        var variableId = variableIds[v];
        var variableConstraints = variables[variableId];
        var cost = variableConstraints[objectiveName] || 0;
        var isBinary = !!binaryVarIds[variableId];
        var isInteger = !!integerVarIds[variableId] || isBinary;
        var isUnrestricted = !!unrestrictedVarIds[variableId];
        var variable = this.addVariable(cost, variableId, isInteger, isUnrestricted);

        if (isBinary) {
            // Creating an upperbound constraint for this variable
            this.smallerThan(1).addTerm(1, variable);
        }

        var constraintNames = Object.keys(variableConstraints);
        for (c = 0; c < constraintNames.length; c += 1) {
            var constraintName = constraintNames[c];
            if (constraintName === objectiveName) {
                continue;
            }

            var coefficient = variableConstraints[constraintName];

            var constraintMin = constraintsMin[constraintName];
            if (constraintMin !== undefined) {
                constraintMin.addTerm(coefficient, variable);
            }

            var constraintMax = constraintsMax[constraintName];
            if (constraintMax !== undefined) {
                constraintMax.addTerm(coefficient, variable);
            }
        }
    }

    return this;
};

//-------------------------------------------------------------------
//-------------------------------------------------------------------
Model.prototype.getNumberOfIntegerVariables = function () {
    return this.integerVariables.length;
};

Model.prototype.solve = function () {
    // Setting tableau if not done
    if (this.tableauInitialized === false) {
        this.tableau.setModel(this);
        this.tableauInitialized = true;
    }

    return this.tableau.solve();
};

Model.prototype.isFeasible = function () {
    return this.tableau.feasible;
};

Model.prototype.save = function () {
    return this.tableau.save();
};

Model.prototype.restore = function () {
    return this.tableau.restore();
};

Model.prototype.activateMIRCuts = function (useMIRCuts) {
    this.useMIRCuts = useMIRCuts;
};

Model.prototype.activateRevisedSimplex = function (useRevisedSimplex) {
    this.useRevisedSimplex = useRevisedSimplex;
};

Model.prototype.debug = function (debugCheckForCycles) {
    this.checkForCycles = debugCheckForCycles;
};

Model.prototype.log = function (message) {
    return this.tableau.log(message);
};

},{"./Tableau/Tableau.js":7,"./Tableau/branchAndCut.js":9,"./expressions.js":18}],2:[function(require,module,exports){
/*global describe*/
/*global require*/
/*global module*/
/*global it*/
/*global console*/
/*global process*/

    /***************************************************************
     * Method: polyopt
     * Scope: private
     * Agruments:
     *        model: The model we want solver to operate on.
                     Because we're in here, we're assuming that
                     we're solving a multi-objective optimization
                     problem. Poly-Optimization. polyopt.

                     This model has to be formed a little differently
                     because it has multiple objective functions.
                     Normally, a model has 2 attributes: opType (string,
                     "max" or "min"), and optimize (string, whatever
                     attribute we're optimizing.

                     Now, there is no opType attribute on the model,
                     and optimize is an object of attributes to be
                     optimized, and how they're to be optimized.
                     For example:

                     ...
                     "optimize": {
                        "pancakes": "max",
                        "cost": "minimize"
                     }
                     ...


     **************************************************************/

module.exports = function(solver, model){

    // I have no idea if this is actually works, or what,
    // but here is my algorithm to solve linear programs
    // with multiple objective functions

    // 1. Optimize for each constraint
    // 2. The results for each solution is a vector
    //    representing a vertex on the polytope we're creating
    // 3. The results for all solutions describes the shape
    //    of the polytope (would be nice to have the equation
    //    representing this)
    // 4. Find the mid-point between all vertices by doing the
    //    following (a_1 + a_2 ... a_n) / n;
    var objectives = model.optimize,
        new_constraints = JSON.parse(JSON.stringify(model.optimize)),
        keys = Object.keys(model.optimize),
        tmp,
        counter = 0,
        vectors = {},
        vector_key = "",
        obj = {},
        pareto = [],
        i,j,x,y,z;

    // Delete the optimize object from the model
    delete model.optimize;

    // Iterate and Clear
    for(i = 0; i < keys.length; i++){
        // Clean up the new_constraints
        new_constraints[keys[i]] = 0;
    }

    // Solve and add
    for(i = 0; i < keys.length; i++){

        // Prep the model
        model.optimize = keys[i];
        model.opType = objectives[keys[i]];

        // solve the model
        tmp = solver.Solve(model, undefined, undefined, true);

        // Only the variables make it into the solution;
        // not the attributes.
        //
        // Because of this, we have to add the attributes
        // back onto the solution so we can do math with
        // them later...

        // Loop over the keys
        for(y in keys){
            // We're only worried about attributes, not variables
            if(!model.variables[keys[y]]){
                // Create space for the attribute in the tmp object
                tmp[keys[y]] = tmp[keys[y]] ? tmp[keys[y]] : 0;
                // Go over each of the variables
                for(x in model.variables){
                    // Does the variable exist in tmp *and* does attribute exist in this model?
                    if(model.variables[x][keys[y]] && tmp[x]){
                        // Add it to tmp
                        tmp[keys[y]] += tmp[x] * model.variables[x][keys[y]];
                    }
                }
            }
        }

        // clear our key
        vector_key = "base";
        // this makes sure that if we get
        // the same vector more than once,
        // we only count it once when finding
        // the midpoint
        for(j = 0; j < keys.length; j++){
            if(tmp[keys[j]]){
                vector_key += "-" + ((tmp[keys[j]] * 1000) | 0) / 1000;
            } else {
                vector_key += "-0";
            }
        }

        // Check here to ensure it doesn't exist
        if(!vectors[vector_key]){
            // Add the vector-key in
            vectors[vector_key] = 1;
            counter++;
            
            // Iterate over the keys
            // and update our new constraints
            for(j = 0; j < keys.length; j++){
                if(tmp[keys[j]]){
                    new_constraints[keys[j]] += tmp[keys[j]];
                }
            }
            
            // Push the solution into the paretos
            // array after cleaning it of some
            // excess data markers
            
            delete tmp.feasible;
            delete tmp.result;            
            pareto.push(tmp);
        }
    }

    // Trying to find the mid-point
    // divide each constraint by the
    // number of constraints
    // *midpoint formula*
    // (x1 + x2 + x3) / 3
    for(i = 0; i < keys.length; i++){
        model.constraints[keys[i]] = {"equal": new_constraints[keys[i]] / counter};
    }

    // Give the model a fake thing to optimize on
    model.optimize = "cheater-" + Math.random();
    model.opType = "max";

    // And add the fake attribute to the variables
    // in the model
    for(i in model.variables){
        model.variables[i].cheater = 1;
    }
    
    // Build out the object with all attributes
    for(i in pareto){
        for(x in pareto[i]){
            obj[x] = obj[x] || {min: 1e99, max: -1e99};
        }
    }
    
    // Give each pareto a full attribute list
    // while getting the max and min values
    // for each attribute
    for(i in obj){
        for(x in pareto){
            if(pareto[x][i]){
                if(pareto[x][i] > obj[i].max){
                    obj[i].max = pareto[x][i];
                } 
                if(pareto[x][i] < obj[i].min){
                    obj[i].min = pareto[x][i];
                }
            } else {
                pareto[x][i] = 0;
                obj[i].min = 0;
            }
        }
    }
    // Solve the model for the midpoints
    tmp =  solver.Solve(model, undefined, undefined, true);
    
    return {
        midpoint: tmp,
        vertices: pareto,
        ranges: obj
    };    

};

},{}],3:[function(require,module,exports){
/*global describe*/
/*global require*/
/*global module*/
/*global it*/
/*global console*/
/*global process*/
/*jshint -W083 */






 /*************************************************************
 * Method: to_JSON
 * Scope: Public:
 * Agruments: input: Whatever the user gives us
 * Purpose: Convert an unfriendly formatted LP
 *          into something that our library can
 *          work with
 **************************************************************/
function to_JSON(input){
    var rxo = {
        /* jshint ignore:start */
        "is_blank": /^\W{0,}$/,
        "is_objective": /(max|min)(imize){0,}\:/i,
        //previous version
        //"is_int": /^\W{0,}int/i,
        //new version to avoid comments
        "is_int": /^(?!\/\*)\W{0,}int/i,
        "is_constraint": /(\>|\<){0,}\=/i,
        "is_unrestricted": /^\S{0,}unrestricted/i,
        "parse_lhs":  /(\-|\+){0,1}\s{0,1}\d{0,}\.{0,}\d{0,}\s{0,}[A-Za-z]\S{0,}/gi,
        "parse_rhs": /(\-|\+){0,1}\d{1,}\.{0,}\d{0,}\W{0,}\;{0,1}$/i,
        "parse_dir": /(\>|\<){0,}\=/gi,
        "parse_int": /[^\s|^\,]+/gi,
        "get_num": /(\-|\+){0,1}(\W|^)\d+\.{0,1}\d{0,}/g, // Why accepting character \W before the first digit?
        "get_word": /[A-Za-z].*/
        /* jshint ignore:end */
    },
    model = {
        "opType": "",
        "optimize": "_obj",
        "constraints": {},
        "variables": {}
    },
    constraints = {
        ">=": "min",
        "<=": "max",
        "=": "equal"
    },
    tmp = "", tst = 0, ary = null, hldr = "", hldr2 = "",
    constraint = "", rhs = 0;

    // Handle input if its coming
    // to us as a hard string
    // instead of as an array of
    // strings
    if(typeof input === "string"){
        input = input.split("\n");
    }

    // Start iterating over the rows
    // to see what all we have
    for(var i = 0; i < input.length; i++){

        constraint = "__" + i;

        // Get the string we're working with
        tmp = input[i];

        // Set the test = 0
        tst = 0;

        // Reset the array
        ary = null;

        // Test to see if we're the objective
        if(rxo.is_objective.test(tmp)){
            // Set up in model the opType
            model.opType = tmp.match(/(max|min)/gi)[0];

            // Pull apart lhs
            ary = tmp.match(rxo.parse_lhs).map(function(d){
                return d.replace(/\s+/,"");
            }).slice(1);



            // *** STEP 1 *** ///
            // Get the variables out
            ary.forEach(function(d){

                // Get the number if its there
                hldr = d.match(rxo.get_num);

                // If it isn't a number, it might
                // be a standalone variable
                if(hldr === null){
                    if(d.substr(0,1) === "-"){
                        hldr = -1;
                    } else {
                        hldr = 1;
                    }
                } else {
                    hldr = hldr[0];
                }

                hldr = parseFloat(hldr);

                // Get the variable type
                hldr2 = d.match(rxo.get_word)[0].replace(/\;$/,"");

                // Make sure the variable is in the model
                model.variables[hldr2] = model.variables[hldr2] || {};
                model.variables[hldr2]._obj = hldr;

            });
        ////////////////////////////////////
        }else if(rxo.is_int.test(tmp)){
            // Get the array of ints
            ary = tmp.match(rxo.parse_int).slice(1);

            // Since we have an int, our model should too
            model.ints = model.ints || {};

            ary.forEach(function(d){
                d = d.replace(";","");
                model.ints[d] = 1;
            });
        ////////////////////////////////////
        } else if(rxo.is_constraint.test(tmp)){
            var separatorIndex = tmp.indexOf(":");
            var constraintExpression = (separatorIndex === -1) ? tmp : tmp.slice(separatorIndex + 1);

            // Pull apart lhs
            ary = constraintExpression.match(rxo.parse_lhs).map(function(d){
                return d.replace(/\s+/,"");
            });

            // *** STEP 1 *** ///
            // Get the variables out
            ary.forEach(function(d){
                // Get the number if its there
                hldr = d.match(rxo.get_num);

                if(hldr === null){
                    if(d.substr(0,1) === "-"){
                        hldr = -1;
                    } else {
                        hldr = 1;
                    }
                } else {
                    hldr = hldr[0];
                }

                hldr = parseFloat(hldr);


                // Get the variable name
                hldr2 = d.match(rxo.get_word)[0];

                // Make sure the variable is in the model
                model.variables[hldr2] = model.variables[hldr2] || {};
                model.variables[hldr2][constraint] = hldr;

            });

            // *** STEP 2 *** ///
            // Get the RHS out
            rhs = parseFloat(tmp.match(rxo.parse_rhs)[0]);

            // *** STEP 3 *** ///
            // Get the Constrainer out
            tmp = constraints[tmp.match(rxo.parse_dir)[0]];
            model.constraints[constraint] = model.constraints[constraint] || {};
            model.constraints[constraint][tmp] = rhs;
        ////////////////////////////////////
        } else if(rxo.is_unrestricted.test(tmp)){
            // Get the array of unrestricted
            ary = tmp.match(rxo.parse_int).slice(1);

            // Since we have an int, our model should too
            model.unrestricted = model.unrestricted || {};

            ary.forEach(function(d){
                d = d.replace(";","");
                model.unrestricted[d] = 1;
            });
        }
    }
    return model;
}


 /*************************************************************
 * Method: from_JSON
 * Scope: Public:
 * Agruments: model: The model we want solver to operate on
 * Purpose: Convert a friendly JSON model into a model for a
 *          real solving library...in this case
 *          lp_solver
 **************************************************************/
function from_JSON(model){
    // Make sure we at least have a model
    if (!model) {
        throw new Error("Solver requires a model to operate on");
    }

    var output = "",
        ary = [],
        norm = 1,
        lookup = {
            "max": "<=",
            "min": ">=",
            "equal": "="
        },
        rxClean = new RegExp("[^A-Za-z0-9]+", "gi");

    // Build the objective statement
    output += model.opType + ":";

    // Iterate over the variables
    for(var x in model.variables){
        // Give each variable a self of 1 unless
        // it exists already
        model.variables[x][x] = model.variables[x][x] ? model.variables[x][x] : 1;

        // Does our objective exist here?
        if(model.variables[x][model.optimize]){
            output += " " + model.variables[x][model.optimize] + " " + x.replace(rxClean,"_");
        }
    }

    // Add some closure to our line thing
    output += ";\n";

    // And now... to iterate over the constraints
    for(x in model.constraints){
        for(var y in model.constraints[x]){
            for(var z in model.variables){
                // Does our Constraint exist here?
                if(model.variables[z][x]){
                    output += " " + model.variables[z][x] + " " + z.replace(rxClean,"_");
                }
            }
            // Add the constraint type and value...
            output += " " + lookup[y] + " " + model.constraints[x][y];
            output += ";\n";
        }
    }

    // Are there any ints?
    if(model.ints){
        output += "\n\n";
        for(x in model.ints){
            output += "int " + x.replace(rxClean,"_") + ";\n";
        }
    }

    // Are there any unrestricted?
    if(model.unrestricted){
        output += "\n\n";
        for(x in model.unrestricted){
            output += "unrestricted " + x.replace(rxClean,"_") + ";\n";
        }
    }

    // And kick the string back
    return output;
}


module.exports = function (model) {
    // If the user is giving us an array
    // or a string, convert it to a JSON Model
    // otherwise, spit it out as a string
    if(model.length){
        return to_JSON(model);
    } else {
        return from_JSON(model);
    }
};

},{}],4:[function(require,module,exports){
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

	// Forward solve Ly = b
	var ROW = 0;
	for (i = 0; i < n; i++) {
		y[i] = b[i];
		for (j = 0; j < i; j++) {
			y[i] -= L[i][j] * y[j];
		}
		y[i] /= L[i][i];
	}

	var invLXa_q = y.slice();

	// Backward solve Ux = y
	for (i = n - 1; i >= 0; i--) {
		x[i] = y[i];
		for (j = i + 1; j < n; j++) {
			x[i] -= U[i][j] * x[j];
		}
		x[i] /= U[i][i];
	}

	return [x, invLXa_q];
};


// used for debugging
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

Tableau.prototype.LUEvaluateRow = function (L, U, N, r) {
	var height = this.height - 1;
	var width = this.width - 1;
	var col = new Array(height);
	var row = new Array(width);

	for (var i = 0; i < width; i++) {
		for (var j = 0; j < height; j++) {
			col[j] = N[j + 1][i + 1];
		}
		row[i] = this.LUEvaluate(L, U, col)[0][r - 1];
	}

	return row;
};

Tableau.prototype.LUEvaluateMatrix = function (L, U) {
	var height = this.height - 1;
	var width = this.width - 1;

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
	var PLU = this.decompose2(B, b);

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

    while (true) {
		console.log("ITERATION PHASE 1", iterations);

		var debugLog = false;

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
		for (var rc = 0; rc < this.width - 1; rc++) {
			updated_cN[rc] -= tmpVect[rc];
		}


		// Compute the row according to the current basis
		// TODO : optimize
		var leavingRow = this.LUEvaluateRow(LU[0], LU[1], N, leavingRowIndex);

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
		var aqInfo = this.LUEvaluate(LU[0], LU[1], aq);

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

		rhsValue = updated_b[leavingRowIndex - 1];
		var colValue = aqInfo[0][leavingRowIndex - 1];


		var minRatio = rhsValue / colValue;

		console.log(leavingRowIndex, enteringColumn);

		this.revisedPivot(leavingRowIndex - 1, enteringColumn - 1, updated_b, cN, LU, LU_T, aqInfo, originalZ, minRatio);
		iterations += 1;
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

	var b = this.originalRHS.slice();

	var LU = this.decompose2(B, b);
	var LU_T = this.decompose(transposeMatrix(B));

	this.LU = LU;
	this.LU_T = LU_T;

	var cN = N[0].slice(1);

	var updated_b = this.LUEvaluate(LU[0], LU[1], b)[0];

	var reducedCost, unrestricted;

	console.log("START");

	while(true) {
		console.log("ITERATION PHASE 2", iter);

		var debugLog = false;

		var optionalCostsColumns = null;
		if (nOptionalObjectives > 0) {
			optionalCostsColumns = [];
		}

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
						optionalCostsColumns2.push(c);
						continue;
					}

					if (unrestricted && tmpCost < 0) {
						if (-tmpCost > enteringValue + precision) {
							enteringValue = -tmpCost;
							enteringColumn = c;
							isReducedCostNegative = true;
						}
						continue;
					}

					if (tmpCost > enteringValue + precision) {
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
		var aqInfo = this.LUEvaluate(LU[0], LU[1], aq);
		var updated_aq = aqInfo[0];
		var invLXa_q = aqInfo[1];


		var minQuotient = Infinity;
		var leavingRow = -1;

		for (r = 0; r < updated_b.length; r++) {
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

		var tmpLeavingRow = this.LUEvaluateRow(LU[0], LU[1], N, leavingRow);


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

		console.log(leavingRow + 1, enteringColumn + 1);
		this.revisedPivot(leavingRow, enteringColumn, updated_b, cN, LU, LU_T, aqInfo, originalZ, minQuotient);

		iter++;
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
		b[r] -= minQuotient * updated_aq[r];
		N[r + 1][0] = b[r];
	}
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
		var i, tmp;
		var N = this.matrix;
		var B = this.basis;
		for (i = 0; i < this.height - 1; i++) {
			tmp = B[row1 - 1][i];
			B[row1 - 1][i] = B[row2 - 1][i];
			B[row2 - 1][i] = tmp;
		}

		for (i = 0; i < this.width; i++) {
			tmp = N[row1][i];
			N[row1][i] = N[row2][i];
			N[row2][i] = tmp;
		}

		var basicIndex1 = this.varIndexByRow[row1];
		var basicIndex2 = this.varIndexByRow[row2];

		tmp = this.originalRHS[row1 - 1];
		this.originalRHS[row1 - 1] = this.originalRHS[row2 - 1];
		this.originalRHS[row2 - 1] = tmp;
	}
};

Tableau.prototype.switchBasicColumns = function (col1, col2) {
	if (col1 !== col2) {
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
	}
}

},{"./Tableau.js":7}],5:[function(require,module,exports){
/*global module*/
/*global require*/
var Solution = require("./Solution.js");

function MilpSolution(tableau, evaluation, feasible, bounded, branchAndCutIterations) {
    Solution.call(this, tableau, evaluation, feasible, bounded);
    this.iter = branchAndCutIterations;
}
module.exports = MilpSolution;
MilpSolution.prototype = Object.create(Solution.prototype);
MilpSolution.constructor = MilpSolution;

},{"./Solution.js":6}],6:[function(require,module,exports){
/*global module*/

function Solution(tableau, evaluation, feasible, bounded) {
    this.feasible = feasible;
    this.evaluation = evaluation;
    this.bounded = bounded;
    this._tableau = tableau;
}
module.exports = Solution;

Solution.prototype.generateSolutionSet = function () {
    var solutionSet = {};

    var tableau = this._tableau;
    var varIndexByRow = tableau.varIndexByRow;
    var variablesPerIndex = tableau.variablesPerIndex;
    var matrix = tableau.matrix;
    var rhsColumn = tableau.rhsColumn;
    var lastRow = tableau.height - 1;
    var roundingCoeff = Math.round(1 / tableau.precision);

    for (var r = 1; r <= lastRow; r += 1) {
        var varIndex = varIndexByRow[r];
        var variable = variablesPerIndex[varIndex];
        if (variable === undefined || variable.isSlack === true) {
            continue;
        }

        var varValue = matrix[r][rhsColumn];
        solutionSet[variable.id] =
            Math.round(varValue * roundingCoeff) / roundingCoeff;
    }

    return solutionSet;
};

},{}],7:[function(require,module,exports){
/*global describe*/
/*global require*/
/*global module*/
/*global it*/
/*global console*/
/*global process*/
var Solution = require("./Solution.js");
var MilpSolution = require("./MilpSolution.js");

/*************************************************************
 * Class: Tableau
 * Description: Simplex tableau, holding a the tableau matrix
 *              and all the information necessary to perform
 *              the simplex algorithm
 * Agruments:
 *        precision: If we're solving a MILP, how tight
 *                   do we want to define an integer, given
 *                   that 20.000000000000001 is not an integer.
 *                   (defaults to 1e-8)
 **************************************************************/
function Tableau(precision) {
    this.model = null;

    this.matrix = null;
    this.width = 0;
    this.height = 0;

    this.costRowIndex = 0;
    this.rhsColumn = 0;

    this.variablesPerIndex = [];
    this.unrestrictedVars = null;

    // Solution attributes
    this.feasible = true; // until proven guilty
    this.evaluation = 0;

    this.varIndexByRow = null;
    this.varIndexByCol = null;

    this.rowByVarIndex = null;
    this.colByVarIndex = null;

    this.precision = precision || 1e-8;

    this.optionalObjectives = [];
    this.objectivesByPriority = {};

    this.savedState = null;

    this.availableIndexes = [];
    this.lastElementIndex = 0;

    this.variables = null;
    this.nVars = 0;

    this.bounded = true;
    this.unboundedVarIndex = null;

    this.branchAndCutIterations = 0;

    this.basis = [];
    this.basisCosts = [];
    this.nextBasisIndex = 0;
    this.basisOptionalCosts = null;
    this.originalRHS = [];
    this.originalZ = 0;
    this.tmpL = new Array(0);
    this.tmpU = new Array(0);


    // get rid of it (in simplex)
    this.tmpIter = 0;
}
module.exports = Tableau;

Tableau.prototype.solve = function () {
    if (this.model.getNumberOfIntegerVariables() > 0) {
        this.branchAndCut();
    } else {
        this.simplex();
    }
    this.updateVariableValues();
    return this.getSolution();
};

function OptionalObjective(priority, nColumns) {
    this.priority = priority;
    this.reducedCosts = new Array(nColumns);
    for (var c = 0; c < nColumns; c += 1) {
        this.reducedCosts[c] = 0;
    }
}

OptionalObjective.prototype.copy = function () {
    var copy = new OptionalObjective(this.priority, this.reducedCosts.length);
    copy.reducedCosts = this.reducedCosts.slice();
    return copy;
};

Tableau.prototype.setOptionalObjective = function (priority, column, cost) {
    var useRevisedSimplex = this.model.useRevisedSimplex;
    var objectiveForPriority = this.objectivesByPriority[priority];
    if (objectiveForPriority === undefined) {
        var nColumns = Math.max(this.width, column + 1);
        objectiveForPriority = new OptionalObjective(priority, nColumns);
        this.objectivesByPriority[priority] = objectiveForPriority;
        this.optionalObjectives.push(objectiveForPriority);
        this.optionalObjectives.sort(function (a, b) {
            return a.priority - b.priority;
        });

        if (useRevisedSimplex) {
            if (this.basisOptionalCosts === null) {
                this.basisOptionalCosts = new Array(1);
                this.basisOptionalCosts[0] = this.basisCosts.slice();
            } else {
                this.basisOptionalCosts.push(this.basisCosts.slice());
            }
        }
    }

    objectiveForPriority.reducedCosts[column] = cost;
};

//-------------------------------------------------------------------
//-------------------------------------------------------------------
Tableau.prototype.initialize = function (width, height, variables, unrestrictedVars) {
    this.variables = variables;
    this.unrestrictedVars = unrestrictedVars;

    this.width = width;
    this.height = height;

    // BUILD AN EMPTY ARRAY OF THAT WIDTH
    var tmpRow = new Array(width);
    for (var i = 0; i < width; i++) {
        tmpRow[i] = 0;
    }

    // BUILD AN EMPTY TABLEAU
    this.matrix = new Array(height);
    for (var j = 0; j < height; j++) {
        this.matrix[j] = tmpRow.slice();
    }

    this.varIndexByRow = new Array(this.height);
    this.varIndexByCol = new Array(this.width);

    this.varIndexByRow[0] = -1;
    this.varIndexByCol[0] = -1;

    this.nVars = width + height - 2;
    this.rowByVarIndex = new Array(this.nVars);
    this.colByVarIndex = new Array(this.nVars);

    this.lastElementIndex = this.nVars;
};

Tableau.prototype._resetMatrix = function () {
    var variables = this.model.variables;
    var constraints = this.model.constraints;

    var nVars = variables.length;
    var nConstraints = constraints.length;

    var v, varIndex;
    var costRow = this.matrix[0];
    var coeff = (this.model.isMinimization === true) ? -1 : 1;
    for (v = 0; v < nVars; v += 1) {
        var variable = variables[v];
        var priority = variable.priority;
        var cost = coeff * variable.cost;
        if (priority === 0) {
            costRow[v + 1] = cost;
        } else {
            this.setOptionalObjective(priority, v + 1, cost);
        }

        varIndex = variables[v].index;
        this.rowByVarIndex[varIndex] = -1;
        this.colByVarIndex[varIndex] = v + 1;
        this.varIndexByCol[v + 1] = varIndex;
    }

    var rowIndex = 1;
    for (var c = 0; c < nConstraints; c += 1) {
        var constraint = constraints[c];

        var constraintIndex = constraint.index;
        this.rowByVarIndex[constraintIndex] = rowIndex;
        this.colByVarIndex[constraintIndex] = -1;
        this.varIndexByRow[rowIndex] = constraintIndex;

        var t, term, column;
        var terms = constraint.terms;
        var nTerms = terms.length;
        var row = this.matrix[rowIndex++];
        if (constraint.isUpperBound) {
            for (t = 0; t < nTerms; t += 1) {
                term = terms[t];
                column = this.colByVarIndex[term.variable.index];
                row[column] = term.coefficient;
            }

            row[0] = constraint.rhs;
            if (this.model.useRevisedSimplex) {
                this.originalRHS[rowIndex - 2] = constraint.rhs;
            }
        } else {
            for (t = 0; t < nTerms; t += 1) {
                term = terms[t];
                column = this.colByVarIndex[term.variable.index];
                row[column] = -term.coefficient;
            }

            row[0] = -constraint.rhs;
            if (this.model.useRevisedSimplex) {
                this.originalRHS[rowIndex - 2] = -constraint.rhs;
            }
        }
    }
};

//-------------------------------------------------------------------
//-------------------------------------------------------------------
Tableau.prototype.setModel = function (model) {
    this.model = model;

    var width = model.nVariables + 1;
    var height = model.nConstraints + 1;


    this.initialize(width, height, model.variables, model.unrestrictedVariables);
    this._resetMatrix();
    return this;
};

Tableau.prototype.getNewElementIndex = function () {
    if (this.availableIndexes.length > 0) {
        return this.availableIndexes.pop();
    }

    var index = this.lastElementIndex;
    this.lastElementIndex += 1;
    return index;
};

Tableau.prototype.density = function () {
    var density = 0;

    var matrix = this.matrix;
    for (var r = 0; r < this.height; r++) {
        var row = matrix[r];
        for (var c = 0; c < this.width; c++) {
            if (row[c] !== 0) {
                density += 1;
            }
        }
    }

    return density / (this.height * this.width);
};

//-------------------------------------------------------------------
//-------------------------------------------------------------------
Tableau.prototype.setEvaluation = function () {
    // Rounding objective value
    var roundingCoeff = Math.round(1 / this.precision);
    var evaluation = this.matrix[this.costRowIndex][this.rhsColumn];
    this.evaluation =
        Math.round(evaluation * roundingCoeff) / roundingCoeff;
};

//-------------------------------------------------------------------
//-------------------------------------------------------------------
Tableau.prototype.getSolution = function () {
    var evaluation = (this.model.isMinimization === true) ?
        this.evaluation : -this.evaluation;

    if (this.model.getNumberOfIntegerVariables() > 0) {
        return new MilpSolution(this, evaluation, this.feasible, this.bounded, this.branchAndCutIterations);
    } else {
        return new Solution(this, evaluation, this.feasible, this.bounded);
    }
};

},{"./MilpSolution.js":5,"./Solution.js":6}],8:[function(require,module,exports){
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

},{"./Tableau.js":7}],9:[function(require,module,exports){
/*global describe*/
/*global require*/
/*global module*/
/*global it*/
/*global console*/
/*global process*/
var Tableau = require("./Tableau.js");

//-------------------------------------------------------------------
//-------------------------------------------------------------------
function Cut(type, varIndex, value) {
    this.type = type;
    this.varIndex = varIndex;
    this.value = value;
}

//-------------------------------------------------------------------
//-------------------------------------------------------------------
function Branch(relaxedEvaluation, cuts) {
    this.relaxedEvaluation = relaxedEvaluation;
    this.cuts = cuts;
}

//-------------------------------------------------------------------
// Branch sorting strategies
//-------------------------------------------------------------------
function sortByEvaluation(a, b) {
    return b.relaxedEvaluation - a.relaxedEvaluation;
}


//-------------------------------------------------------------------
// Applying cuts on a tableau and resolving
//-------------------------------------------------------------------
Tableau.prototype.applyCuts = function (branchingCuts){
    // Restoring initial solution
    this.restore();

    this.addCutConstraints(branchingCuts);
    this.simplex();
    // Adding MIR cuts
    if (this.model.useMIRCuts){
        var fractionalVolumeImproved = true;
        while(fractionalVolumeImproved){
            var fractionalVolumeBefore = this.computeFractionalVolume(true);
            this.applyMIRCuts();
            this.simplex();

            var fractionalVolumeAfter = this.computeFractionalVolume(true);

            // If the new fractional volume is bigger than 90% of the previous one
            // we assume there is no improvement from the MIR cuts
            if(fractionalVolumeAfter >= 0.9 * fractionalVolumeBefore){
                fractionalVolumeImproved = false;
            }
        }
    }
};

//-------------------------------------------------------------------
// Function: MILP
// Detail: Main function, my attempt at a mixed integer linear programming
//         solver
//-------------------------------------------------------------------
Tableau.prototype.branchAndCut = function () {
    var branches = [];
    // this.branchAndCutIterations = 0;

    // This is the default result
    // If nothing is both *integral* and *feasible*
    var bestEvaluation = Infinity;
    var bestBranch = null;
    var bestOptionalObjectivesEvaluations = [];
    for (var oInit = 0; oInit < this.optionalObjectives.length; oInit += 1){
        bestOptionalObjectivesEvaluations.push(Infinity);
    }

    // And here...we...go!

    // 1.) Load a model into the queue
    var branch = new Branch(-Infinity, []);

    if (!this.model.useRevisedSimplex) {
        var tmpRHS = [];
        for (var i = 1; i < this.height; i++) {
            tmpRHS.push(this.matrix[i][0]);
        }
    }


    branches.push(branch);

    // If all branches have been exhausted terminate the loop
    while (branches.length > 0) {
        // Get a model from the queue
        // console.log("BRANCHES", JSON.stringify(branches));
        branch = branches.pop();
        if (branch.relaxedEvaluation > bestEvaluation) {
            continue;
        }

        // Solving from initial relaxed solution
        // with additional cut constraints

        // Adding cut constraints
        var cuts = branch.cuts;
        // console.log("CUTS");
        // for(var loop = 0; loop < cuts.length; loop){
        //     console.log(cuts[loop].type, " ", cuts[loop].value);
        // }
        // console.log("\n");

        // console.log();
        // console.log("NEW BRANCH N CUT", this.branchAndCutIterations);
        this.applyCuts(cuts);

        this.branchAndCutIterations++;

        // if (this.branchAndCutIterations === 3) {
        //     throw true;
        // }

        if (this.feasible === false) {
            continue;
        }

        var evaluation = this.evaluation;
        if (evaluation > bestEvaluation) {
            // This branch does not contain the optimal solution
            continue;
        }

        // To deal with the optional objectives
        if (evaluation === bestEvaluation){
            var isCurrentEvaluationWorse = true;
            for (var o = 0; o < this.optionalObjectives.length; o += 1){
                if (this.optionalObjectives[o].reducedCosts[0] > bestOptionalObjectivesEvaluations[o]){
                    break;
                } else if (this.optionalObjectives[o].reducedCosts[0] < bestOptionalObjectivesEvaluations[o]) {
                    isCurrentEvaluationWorse = false;
                    break;
                }
            }

            if (isCurrentEvaluationWorse){
                continue;
            }
        }

        // console.log("change best branch ?", bestEvaluation, evaluation, this.branchAndCutIterations);

        // Is the model both integral and feasible?
        if (this.isIntegral() === true) {
            if (this.branchAndCutIterations === 1) {
                return;
            }
            // Store the solution as the bestSolution
            bestBranch = branch;
            bestEvaluation = evaluation;
            for (var oCopy = 0; oCopy < this.optionalObjectives.length; oCopy += 1){
                bestOptionalObjectivesEvaluations[oCopy] = this.optionalObjectives[oCopy].reducedCosts[0];
            }
        } else {
            if (this.branchAndCutIterations === 1) {
                // Saving the first iteration
                // TODO: implement a better strategy for saving the tableau?
                this.save();
            }


            // If the solution is
            //  a. Feasible
            //  b. Better than the current solution
            //  c. but *NOT* integral

            // So the solution isn't integral? How do we solve this.
            // We create 2 new models, that are mirror images of the prior
            // model, with 1 exception.

            // Say we're trying to solve some stupid problem requiring you get
            // animals for your daughter's kindergarten petting zoo party
            // and you have to choose how many ducks, goats, and lambs to get.

            // Say that the optimal solution to this problem if we didn't have
            // to make it integral was {duck: 8, lambs: 3.5}
            //
            // To keep from traumatizing your daughter and the other children
            // you're going to want to have whole animals

            // What we would do is find the most fractional variable (lambs)
            // and create new models from the old models, but with a new constraint
            // on apples. The constraints on the low model would look like:
            // constraints: {...
            //   lamb: {max: 3}
            //   ...
            // }
            //
            // while the constraints on the high model would look like:
            //
            // constraints: {...
            //   lamb: {min: 4}
            //   ...
            // }
            // If neither of these models is feasible because of this constraint,
            // the model is not integral at this point, and fails.

            // Find out where we want to split the solution
            var variable = this.getMostFractionalVar();

            var varIndex = variable.index;

            var cutsHigh = [];
            var cutsLow = [];

            var nCuts = cuts.length;
            for (var c = 0; c < nCuts; c += 1) {
                var cut = cuts[c];
                if (cut.varIndex === varIndex) {
                    if (cut.type === "min") {
                        cutsLow.push(cut);
                    } else {
                        cutsHigh.push(cut);
                    }
                } else {
                    cutsHigh.push(cut);
                    cutsLow.push(cut);
                }
            }

            var min = Math.ceil(variable.value);
            var max = Math.floor(variable.value);

            var cutHigh = new Cut("min", varIndex, min);
            cutsHigh.push(cutHigh);
            // console.log("HIGH CUT", cutHigh);

            var cutLow = new Cut("max", varIndex, max);
            cutsLow.push(cutLow);
            // console.log("LOW CUT", cutLow);

            branches.push(new Branch(evaluation, cutsHigh));
            branches.push(new Branch(evaluation, cutsLow));

            // Sorting branches
            // Branches with the most promising lower bounds
            // will be picked first
            branches.sort(sortByEvaluation);
        }
    }

    // Adding cut constraints for the optimal solution
    if (bestBranch !== null) {
        // The model is feasible
        this.applyCuts(bestBranch.cuts);
    }
};

},{"./Tableau.js":7}],10:[function(require,module,exports){
/*global require*/
var Tableau = require("./Tableau.js");

function VariableData(index, value) {
    this.index = index;
    this.value = value;
}

//-------------------------------------------------------------------
//-------------------------------------------------------------------
Tableau.prototype.getMostFractionalVar = function () {
    var biggestFraction = 0;
    var selectedVarIndex = null;
    var selectedVarValue = null;
    var mid = 0.5;

    var integerVariables = this.model.integerVariables;
    var nIntegerVars = integerVariables.length;
    for (var v = 0; v < nIntegerVars; v++) {
        var varIndex = integerVariables[v].index;
        var varRow = this.rowByVarIndex[varIndex];
        if (varRow === -1) {
            continue;
        }

        var varValue = this.matrix[varRow][this.rhsColumn];
        var fraction = Math.abs(varValue - Math.round(varValue));
        if (biggestFraction < fraction) {
            biggestFraction = fraction;
            selectedVarIndex = varIndex;
            selectedVarValue = varValue;
        }
    }

    return new VariableData(selectedVarIndex, selectedVarValue);
};

//-------------------------------------------------------------------
//-------------------------------------------------------------------
Tableau.prototype.getFractionalVarWithLowestCost = function () {
    var highestCost = Infinity;
    var selectedVarIndex = null;
    var selectedVarValue = null;

    var integerVariables = this.model.integerVariables;
    var nIntegerVars = integerVariables.length;
    for (var v = 0; v < nIntegerVars; v++) {
        var variable = integerVariables[v];
        var varIndex = variable.index;
        var varRow = this.rowByVarIndex[varIndex];
        if (varRow === -1) {
            // Variable value is non basic
            // its value is 0
            continue;
        }

        var varValue = this.matrix[varRow][this.rhsColumn];
        if (Math.abs(varValue - Math.round(varValue)) > this.precision) {
            var cost = variable.cost;
            if (highestCost > cost) {
                highestCost = cost;
                selectedVarIndex = varIndex;
                selectedVarValue = varValue;
            }
        }
    }

    return new VariableData(selectedVarIndex, selectedVarValue);
};

},{"./Tableau.js":7}],11:[function(require,module,exports){
/*global require*/
var Tableau = require("./Tableau.js");
var SlackVariable = require("../expressions.js").SlackVariable;

Tableau.prototype.addCutConstraints = function (cutConstraints) {
    var nCutConstraints = cutConstraints.length;

    var height = this.height;
    var heightWithCuts = height + nCutConstraints;

    // Adding rows to hold cut constraints
    var i, j, c, h;
    for (h = height; h < heightWithCuts; h += 1) {
        if (this.matrix[h] === undefined) {
            this.matrix[h] = this.matrix[h - 1].slice();
        }
    }

    var B = this.basis;
    if (this.model.useRevisedSimplex) {
        // Reinitializing values in B
        var nextBasisIndex = this.nextBasisIndex;
        var positionFillUntil = Math.min(B.length, heightWithCuts - 1);
        for (i = 0; i < nextBasisIndex; i++) {
            B[i].fill(0, nextBasisIndex, positionFillUntil);
        }
        for (i = nextBasisIndex; i < positionFillUntil; i++) {
            B[i].fill(0, 0, positionFillUntil);
            B[i][i] = 1;
        }

        var nbElementsToAdd = heightWithCuts - 1 - B.length;
        var fillerArray = [];
        if (nbElementsToAdd > 0) {
            fillerArray = new Array(nbElementsToAdd).fill(0);

            // Adding n columns to B
            for (i = 0; i < positionFillUntil; i++) {
                B[i].push.apply(B[i], fillerArray);
            }

            // Adding n rows to B for the slack variables
            for (h = B.length; h < heightWithCuts - 1; h++) {
                B[h] = new Array(heightWithCuts - 1).fill(0);
                B[h][h] = 1;
            }
        }

        // Adding n entries to the basis costs
        this.basisCosts.fill(0, nextBasisIndex, positionFillUntil);
        this.basisCosts.push.apply(this.basisCosts, fillerArray);

        // Adding n entries to all the optional basis costs
        if (this.basisOptionalCosts !== null) {
            for (i = 0; i < this.basisOptionalCosts.length; i++) {
                var basisOptionalCost = this.basisOptionalCosts[i];
                basisOptionalCost.fill(0, nextBasisIndex, positionFillUntil);
                basisOptionalCost.push.apply(basisOptionalCost, fillerArray);
            }
        }

        // Adding n entries to the original RHS
        this.originalRHS.fill(0, nextBasisIndex, positionFillUntil);
        this.originalRHS.push.apply(this.originalRHS, fillerArray);

        // Update next basis index
        this.nextBasisIndex = heightWithCuts - 1;

    }


    // Adding cut constraints
    this.height = heightWithCuts;
    this.nVars = this.width + this.height - 2;

    var lastColumn = this.width - 1;
    for (i = 0; i < nCutConstraints; i += 1) {
        var cut = cutConstraints[i];

        // Constraint row index
        var r = height + i;

        var sign = (cut.type === "min") ? -1 : 1;

        // Variable on which the cut is applied
        var varIndex = cut.varIndex;
        var varRowIndex = this.rowByVarIndex[varIndex];
        var constraintRow = this.matrix[r];



        // if (this.model.useRevisedSimplex) {
        //     if (varRowIndex === -1) {
        //         console.log("NON BASIC");
        //         // Variable is non basic
        //         varRowIndex = this._revisedPutInBase(varIndex);
        //     }
        //     // Variable is now basic
        //     var varRow = this.matrix[varRowIndex];
        //     var varValue = varRow[this.rhsColumn];
        //     constraintRow[this.rhsColumn] = sign * (cut.value - varValue);
        //     this.originalRHS[r - 1] = constraintRow[this.rhsColumn];
        //
        //     var b = new Array(this.nextBasisIndex);
        //     for (var j = 1; j <= this.nextBasisIndex; j++) {
        //         b[j - 1] = this.matrix[j][this.rhsColumn];
        //     }
        //     var LU = this.decompose2(B, b);
        //     updatedOriginalRow = this.LUEvaluateRow(LU[0], LU[1], this.matrix, varRowIndex);
        //     for (var j = 1; j < this.width; j++) {
        //         this.matrix[r][j] = updatedOriginalRow[j - 1] * -sign;
        //     }
        // } else {
        //     if (varRowIndex === -1) {
        //         // Variable is non basic
        //         constraintRow[this.rhsColumn] = sign * cut.value;
        //         for (c = 1; c <= lastColumn; c += 1) {
        //             constraintRow[c] = 0;
        //         }
        //         constraintRow[this.colByVarIndex[varIndex]] = sign;
        //     } else {
        //         // Variable is basic
        //         var varRow = this.matrix[varRowIndex];
        //         var varValue = varRow[this.rhsColumn];
        //         constraintRow[this.rhsColumn] = sign * (cut.value - varValue);
        //         for (c = 1; c <= lastColumn; c += 1) {
        //             constraintRow[c] = -sign * varRow[c];
        //         }
        //     }
        // }


        var b;
        var LU;
        if (varRowIndex === -1) {
            // console.log("HERE NON BASIC");
            // Variable is non basic
            constraintRow[this.rhsColumn] = sign * cut.value;
            if (this.model.useRevisedSimplex) {
                b = new Array(this.nextBasisIndex);
                for (j = 1; j < this.height; j++) {
                    b[j - 1] = this.matrix[j][this.rhsColumn];
                }
                LU = this.decompose2(this.basis, b);
                this.originalRHS = this.reverseLUEvaluate(LU[0], LU[1], b);
            }
            for (c = 1; c <= lastColumn; c += 1) {
                constraintRow[c] = 0;
            }
            constraintRow[this.colByVarIndex[varIndex]] = sign;
        } else {
            // console.log("HERE BASIC");
            // Variable is basic
            var varRow = this.matrix[varRowIndex];
            var varValue = varRow[this.rhsColumn];
            constraintRow[this.rhsColumn] = sign * (cut.value - varValue);
            if (this.model.useRevisedSimplex) {
                this.originalRHS[r - 1] = constraintRow[this.rhsColumn];

                b = new Array(this.nextBasisIndex);
                for (j = 1; j <= this.nextBasisIndex; j++) {
                    b[j - 1] = this.matrix[j][this.rhsColumn];
                }
                LU = this.decompose2(B, b);
                var updatedOriginalRow = this.LUEvaluateRow(LU[0], LU[1], this.matrix, varRowIndex);
                for (j = 1; j < this.width; j++) {
                    this.matrix[r][j] = updatedOriginalRow[j - 1] * -sign;
                }
            } else {
                for (c = 1; c <= lastColumn; c += 1) {
                    constraintRow[c] = -sign * varRow[c];
                }
            }
        }


        // Creating slack variable
        var slackVarIndex = this.getNewElementIndex();
        this.varIndexByRow[r] = slackVarIndex;
        this.rowByVarIndex[slackVarIndex] = r;
        this.colByVarIndex[slackVarIndex] = -1;
        this.variablesPerIndex[slackVarIndex] = new SlackVariable("s"+slackVarIndex, slackVarIndex);
        this.nVars += 1;
    }
};

Tableau.prototype._addLowerBoundMIRCut = function(rowIndex) {

	if(rowIndex === this.costRowIndex) {
		//console.log("! IN MIR CUTS : The index of the row corresponds to the cost row. !");
		return false;
	}

	var model = this.model;
	var matrix = this.matrix;

	var intVar = this.variablesPerIndex[this.varIndexByRow[rowIndex]];
	if (!intVar.isInteger) {
		return false;
    }

	var d = matrix[rowIndex][this.rhsColumn];
	var frac_d = d - Math.floor(d);

	if (frac_d < this.precision || 1 - this.precision < frac_d) {
		return false;
    }

	//Adding a row
	var r = this.height;
	matrix[r] = matrix[r - 1].slice();
	this.height += 1;

	// Creating slack variable
	this.nVars += 1;
	var slackVarIndex = this.getNewElementIndex();
	this.varIndexByRow[r] = slackVarIndex;
	this.rowByVarIndex[slackVarIndex] = r;
	this.colByVarIndex[slackVarIndex] = -1;
	this.variablesPerIndex[slackVarIndex] = new SlackVariable("s"+slackVarIndex, slackVarIndex);

	matrix[r][this.rhsColumn] = Math.floor(d);

	for (var colIndex = 1; colIndex < this.varIndexByCol.length; colIndex += 1) {
		var variable = this.variablesPerIndex[this.varIndexByCol[colIndex]];

		if (!variable.isInteger) {
			matrix[r][colIndex] = Math.min(0, matrix[rowIndex][colIndex] / (1 - frac_d));
		} else {
			var coef = matrix[rowIndex][colIndex];
			var termCoeff = Math.floor(coef)+Math.max(0, coef - Math.floor(coef) - frac_d) / (1 - frac_d);
			matrix[r][colIndex] = termCoeff;
		}
	}

	for(var c = 0; c < this.width; c += 1) {
		matrix[r][c] -= matrix[rowIndex][c];
	}

	return true;
};

Tableau.prototype._addUpperBoundMIRCut = function(rowIndex) {

	if (rowIndex === this.costRowIndex) {
		//console.log("! IN MIR CUTS : The index of the row corresponds to the cost row. !");
		return false;
	}

	var model = this.model;
	var matrix = this.matrix;

	var intVar = this.variablesPerIndex[this.varIndexByRow[rowIndex]];
	if (!intVar.isInteger) {
		return false;
    }

	var b = matrix[rowIndex][this.rhsColumn];
	var f = b - Math.floor(b);

	if (f < this.precision || 1 - this.precision < f) {
		return false;
    }

	//Adding a row
	var r = this.height;
	matrix[r] = matrix[r - 1].slice();
	this.height += 1;

	// Creating slack variable
	this.nVars += 1;
	var slackVarIndex = this.getNewElementIndex();
	this.varIndexByRow[r] = slackVarIndex;
	this.rowByVarIndex[slackVarIndex] = r;
	this.colByVarIndex[slackVarIndex] = -1;
	this.variablesPerIndex[slackVarIndex] = new SlackVariable("s" + slackVarIndex, slackVarIndex);

	matrix[r][this.rhsColumn] = -f;

	for(var colIndex = 1; colIndex < this.varIndexByCol.length; colIndex += 1) {
		var variable = this.variablesPerIndex[this.varIndexByCol[colIndex]];

		var aj = matrix[rowIndex][colIndex];
		var fj = aj - Math.floor(aj);

		if(variable.isInteger) {
			if(fj <= f) {
				matrix[r][colIndex] = -fj;
            } else {
				matrix[r][colIndex] = -(1 - fj) * f / fj;
            }
		} else {
			if (aj >= 0) {
				matrix[r][colIndex] = -aj;
            } else {
				matrix[r][colIndex] = aj * f / (1 - f);
            }
		}
	}

	return true;
};

Tableau.prototype.applyMIRCuts = function () {
    var nRows = this.height;
    for (var cst = 0; cst < nRows; cst += 1) {
        this._addUpperBoundMIRCut(cst);
    }

    // nRows = tableau.height;
    for (cst = 0; cst < nRows; cst += 1) {
        this._addLowerBoundMIRCut(cst);
    }
};

},{"../expressions.js":18,"./Tableau.js":7}],12:[function(require,module,exports){
/*global require*/
/*global console*/
var Tableau = require("./Tableau.js");

//-------------------------------------------------------------------
//-------------------------------------------------------------------
Tableau.prototype._putInBase = function (varIndex) {
    // Is varIndex in the base?
    var r = this.rowByVarIndex[varIndex];
    if (r === -1) {
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

        this.pivot(r, c);
    }

    return r;
};

Tableau.prototype._takeOutOfBase = function (varIndex) {
    // Is varIndex in the base?
    var c = this.colByVarIndex[varIndex];
    if (c === -1) {
        // Inside the base
        // pivoting to take it out
        var r = this.rowByVarIndex[varIndex];

        // Selecting pivot column
        // (Any column with coefficient different from 0)
        var pivotRow = this.matrix[r];
        for (var c1 = 1; c1 < this.height; c1 += 1) {
            var coefficient = pivotRow[c1];
            if (coefficient < -this.precision || this.precision < coefficient) {
                c = c1;
                break;
            }
        }

        this.pivot(r, c);
    }

    return c;
};

Tableau.prototype.updateVariableValues = function () {
    var nVars = this.variables.length;
    var roundingCoeff = Math.round(1 / this.precision);
    for (var v = 0; v < nVars; v += 1) {
        var variable = this.variables[v];
        var varIndex = variable.index;

        var r = this.rowByVarIndex[varIndex];
        if (r === -1) {
            // Variable is non basic
            variable.value = 0;
        } else {
            // Variable is basic
            var varValue = this.matrix[r][this.rhsColumn];
            variable.value = Math.round(varValue * roundingCoeff) / roundingCoeff;
        }
    }
};

Tableau.prototype.updateRightHandSide = function (constraint, difference) {
    // Updates RHS of given constraint
    var lastRow = this.height - 1;
    var constraintRow = this.rowByVarIndex[constraint.index];
    if (constraintRow === -1) {
        // Slack is not in base
        var slackColumn = this.colByVarIndex[constraint.index];

        // Upading all the RHS values
        for (var r = 0; r <= lastRow; r += 1) {
            var row = this.matrix[r];
            row[this.rhsColumn] -= difference * row[slackColumn];
        }

        var nOptionalObjectives = this.optionalObjectives.length;
        if (nOptionalObjectives > 0) {
            for (var o = 0; o < nOptionalObjectives; o += 1) {
                var reducedCosts = this.optionalObjectives[o].reducedCosts;
                reducedCosts[this.rhsColumn] -= difference * reducedCosts[slackColumn];
            }
        }
    } else {
        // Slack variable of constraint is in base
        // Updating RHS with the difference between the old and the new one
        this.matrix[constraintRow][this.rhsColumn] -= difference;
    }

    /*************
        TODO
    **************/
    // update basis costs too ?
};

Tableau.prototype.updateConstraintCoefficient = function (constraint, variable, difference) {
    // Updates variable coefficient within a constraint
    if (constraint.index === variable.index) {
        throw new Error("[Tableau.updateConstraintCoefficient] constraint index should not be equal to variable index !");
    }
    var r;

    if (this.model.useRevisedSimplex){
        r = this._revisedPutInBase(constraint.index);
    }
    else{
        r = this._putInBase(constraint.index);
    }

    var colVar = this.colByVarIndex[variable.index];
    if (colVar === -1) {
        var rowVar = this.rowByVarIndex[variable.index];
        for (var c = 0; c < this.width; c += 1){
            this.matrix[r][c] += difference * this.matrix[rowVar][c];
        }
    } else {
        this.matrix[r][colVar] -= difference;
    }
    /*************
        TODO
    **************/
    // update basis costs too ?
};

Tableau.prototype.updateCost = function (variable, difference) {
    // Updates variable coefficient within the objective function
    var varIndex = variable.index;
    var lastColumn = this.width - 1;
    var varColumn = this.colByVarIndex[varIndex];
    if (varColumn === -1) {
        // Variable is in base
        var variableRow = this.matrix[this.rowByVarIndex[varIndex]];

        var c;
        if (variable.priority === 0) {
            var costRow = this.matrix[0];

            // Upading all the reduced costs
            for (c = 0; c <= lastColumn; c += 1) {
                costRow[c] += difference * variableRow[c];
            }
        } else {
            var reducedCosts = this.objectivesByPriority[variable.priority].reducedCosts;
            for (c = 0; c <= lastColumn; c += 1) {
                reducedCosts[c] += difference * variableRow[c];
            }
        }
    } else {
        // Variable is not in the base
        // Updating coefficient with difference
        this.matrix[0][varColumn] -= difference;
    }
    /*************
        TODO
    **************/
    // update basis costs too ?
};

Tableau.prototype.addConstraint = function (constraint) {
    // Adds a constraint to the tableau
    var sign = constraint.isUpperBound ? 1 : -1;
    var lastRow = this.height;

    var constraintRow = this.matrix[lastRow];
    if (constraintRow === undefined) {
        constraintRow = this.matrix[0].slice();
        this.matrix[lastRow] = constraintRow;
    }

    // Setting all row cells to 0
    var lastColumn = this.width - 1;
    for (var c = 0; c <= lastColumn; c += 1) {
        constraintRow[c] = 0;
    }

    // Initializing RHS
    constraintRow[this.rhsColumn] = sign * constraint.rhs;

    var terms = constraint.terms;
    var nTerms = terms.length;
    for (var t = 0; t < nTerms; t += 1) {
        var term = terms[t];
        var coefficient = term.coefficient;
        var varIndex = term.variable.index;

        var varRowIndex = this.rowByVarIndex[varIndex];
        if (varRowIndex === -1) {
            // Variable is non basic
            constraintRow[this.colByVarIndex[varIndex]] += sign * coefficient;
        } else {
            // Variable is basic
            var varRow = this.matrix[varRowIndex];
            var varValue = varRow[this.rhsColumn];
            for (c = 0; c <= lastColumn; c += 1) {
                constraintRow[c] -= sign * coefficient * varRow[c];
            }
        }
    }
    // Creating slack variable
    var slackIndex = constraint.index;
    this.varIndexByRow[lastRow] = slackIndex;
    this.rowByVarIndex[slackIndex] = lastRow;
    this.colByVarIndex[slackIndex] = -1;

    this.height += 1;
};

Tableau.prototype.removeConstraint = function (constraint) {
    var slackIndex = constraint.index;
    var lastRow = this.height - 1;
    var matrix = this.matrix;
    var r;

    if(this.model.useRevisedSimplex){
        var basis = this.basis;
        var tmpVal;
        var nextBasisIndex = this.nextBasisIndex;

        r = this._revisedPutInBase(slackIndex);

        // put slack variable column at the end
        for(var i = 0; i < nextBasisIndex; i++){
            tmpVal = basis[i][r-1];
            basis[i][r-1] = basis[i][nextBasisIndex-1];
            basis[i][nextBasisIndex-1] = tmpVal;
        }

        // put slack variable row at the end
        for(i = 0; i < nextBasisIndex; i++){
            tmpVal = basis[r-1][i];
            basis[r-1][i] = basis[nextBasisIndex-1][i];
            basis[nextBasisIndex-1][i] = tmpVal;
        }

        // Switch basis costs
        var basisCosts = this.basisCosts;
        tmpVal = basisCosts[r-1];
        basisCosts[r-1] = basisCosts[nextBasisIndex-1];
        basisCosts[nextBasisIndex-1] = tmpVal;

        // Switch optional basis costs
        var basisOptionalCosts = this.basisOptionalCosts;
        if(basisOptionalCosts !== null){
            for(i = 0; i < basisOptionalCosts.length; i++){
                tmpVal = basisOptionalCosts[i][r-1];
                basisOptionalCosts[i][r-1] = basisOptionalCosts[i][nextBasisIndex-1];
                basisOptionalCosts[i][nextBasisIndex-1] = tmpVal;
            }
        }

        // Switch in RHS
        tmpVal = this.originalRHS[r-1];
        this.originalRHS[r-1] = this.originalRHS[nextBasisIndex-1];
        this.originalRHS[nextBasisIndex-1] = tmpVal;
        this.originalRHS.splice(nextBasisIndex-1, 1);

        // remove them
        this.nextBasisIndex--;
    }
    else{
        // Putting the constraint's slack in the base
        r = this._putInBase(slackIndex);
    }

    // Removing constraint
    // by putting the corresponding row at the bottom of the matrix
    // and virtually reducing the height of the matrix by 1
    var tmpRow = matrix[lastRow];
    matrix[lastRow] = matrix[r];
    matrix[r] = tmpRow;

    // Removing associated slack variable from basic variables
    this.varIndexByRow[r] = this.varIndexByRow[lastRow];
    this.varIndexByRow[lastRow] = -1;
    this.rowByVarIndex[slackIndex] = -1;

    // Putting associated slack variable index in index manager
    this.availableIndexes[this.availableIndexes.length] = slackIndex;

    constraint.slack.index = -1;

    this.height -= 1;
};

Tableau.prototype.addVariable = function (variable) {
    // Adds a variable to the tableau
    // var sign = constraint.isUpperBound ? 1 : -1;

    var lastRow = this.height - 1;
    var lastColumn = this.width;
    var cost = this.model.isMinimization === true ? -variable.cost : variable.cost;
    var priority = variable.priority;

    // Setting reduced costs
    var nOptionalObjectives = this.optionalObjectives.length;
    if (nOptionalObjectives > 0) {
        for (var o = 0; o < nOptionalObjectives; o += 1) {
            this.optionalObjectives[o].reducedCosts[lastColumn] = 0;
        }
    }

    if (priority === 0) {
        this.matrix[0][lastColumn] = cost;
    } else {
        this.setOptionalObjective(priority, lastColumn, cost);
        this.matrix[0][lastColumn] = 0;
    }

    // Setting all other column cells to 0
    for (var r = 1; r <= lastRow; r += 1) {
        this.matrix[r][lastColumn] = 0;
    }

    // Adding variable to trackers
    var varIndex = variable.index;
    this.varIndexByCol[lastColumn] = varIndex;

    this.rowByVarIndex[varIndex] = -1;
    this.colByVarIndex[varIndex] = lastColumn;

    this.width += 1;

    /*************
        TODO
    **************/
    // update (optional) basis costs too ?
};



Tableau.prototype.removeVariable = function (variable) {
    var varIndex = variable.index;
    var matrix = this.matrix;
    var c;

    if(this.model.useRevisedSimplex){
        c = this._revisedTakeOutOfBase(varIndex);
    }
    else{
        // Putting the variable out of the base
        c = this._takeOutOfBase(varIndex);
    }

    var lastColumn = this.width - 1;
    if (c !== lastColumn) {
        var lastRow = this.height - 1;
        for (var r = 0; r <= lastRow; r += 1) {
            var row = matrix[r];
            row[c] = row[lastColumn];
        }

        var nOptionalObjectives = this.optionalObjectives.length;
        if (nOptionalObjectives > 0) {
            for (var o = 0; o < nOptionalObjectives; o += 1) {
                var reducedCosts = this.optionalObjectives[o].reducedCosts;
                reducedCosts[c] = reducedCosts[lastColumn];
            }
        }

        var switchVarIndex = this.varIndexByCol[lastColumn];
        this.varIndexByCol[c] = switchVarIndex;
        this.colByVarIndex[switchVarIndex] = c;
    }

    // Removing variable from non basic variables
    this.varIndexByCol[lastColumn] = -1;
    this.colByVarIndex[varIndex] = -1;

    // Adding index into index manager
    this.availableIndexes[this.availableIndexes.length] = varIndex;

    variable.index = -1;

    this.width -= 1;

    /*************
        TODO
    **************/
    // update basis costs too ?
};

},{"./Tableau.js":7}],13:[function(require,module,exports){
/*global require*/
/*global module*/
require("./simplex.js");
require("./cuttingStrategies.js");
require("./dynamicModification.js");
require("./log.js");
require("./backup.js");
require("./branchingStrategies.js");
require("./integerProperties.js");

module.exports = require("./Tableau.js");

},{"./Tableau.js":7,"./backup.js":8,"./branchingStrategies.js":10,"./cuttingStrategies.js":11,"./dynamicModification.js":12,"./integerProperties.js":14,"./log.js":15,"./simplex.js":16}],14:[function(require,module,exports){
/*global require*/
var Tableau = require("./Tableau.js");

Tableau.prototype.countIntegerValues = function(){
    var count = 0;
    for (var r = 1; r < this.height; r += 1) {
        if (this.variablesPerIndex[this.varIndexByRow[r]].isInteger) {
            var decimalPart = this.matrix[r][this.rhsColumn];
            decimalPart = decimalPart - Math.floor(decimalPart);
            if (decimalPart < this.precision && -decimalPart < this.precision) {
                count += 1;
            }
        }
    }

    return count;
};

//-------------------------------------------------------------------
//-------------------------------------------------------------------
Tableau.prototype.isIntegral = function () {
    var integerVariables = this.model.integerVariables;

    var nIntegerVars = integerVariables.length;
    for (var v = 0; v < nIntegerVars; v++) {
        var varRow = this.rowByVarIndex[integerVariables[v].index];
        if (varRow === -1) {
            continue;
        }

        var varValue = this.matrix[varRow][this.rhsColumn];
        if (Math.abs(varValue - Math.round(varValue)) > this.precision) {
            return false;
        }
    }
    return true;
};

// Multiply all the fractional parts of variables supposed to be integer
Tableau.prototype.computeFractionalVolume = function(ignoreIntegerValues) {
    var volume = -1;
    // var integerVariables = this.model.integerVariables;
    // var nIntegerVars = integerVariables.length;
    // for (var v = 0; v < nIntegerVars; v++) {
    //     var r = this.rowByVarIndex[integerVariables[v].index];
    //     if (r === -1) {
    //         continue;
    //     }
    //     var rhs = this.matrix[r][this.rhsColumn];
    //     rhs = Math.abs(rhs);
    //     var decimalPart = Math.min(rhs - Math.floor(rhs), Math.floor(rhs + 1));
    //     if (decimalPart < this.precision) {
    //         if (!ignoreIntegerValues) {
    //             return 0;
    //         }
    //     } else {
    //         if (volume === -1) {
    //             volume = rhs;
    //         } else {
    //             volume *= rhs;
    //         }
    //     }
    // }

    for (var r = 1; r < this.height; r += 1) {
        if (this.variablesPerIndex[this.varIndexByRow[r]].isInteger) {
            var rhs = this.matrix[r][this.rhsColumn];
            rhs = Math.abs(rhs);
            var decimalPart = Math.min(rhs - Math.floor(rhs), Math.floor(rhs + 1));
            if (decimalPart < this.precision) {
                if (!ignoreIntegerValues) {
                    return 0;
                }
            } else {
                if (volume === -1) {
                    volume = rhs;
                } else {
                    volume *= rhs;
                }
            }
        }
    }

    if (volume === -1){
        return 0;
    }
    return volume;
};

},{"./Tableau.js":7}],15:[function(require,module,exports){
/*global require*/
/*global console*/
var Tableau = require("./Tableau.js");

//-------------------------------------------------------------------
// Description: Display a tableau matrix
//              and additional tableau information
//
//-------------------------------------------------------------------
Tableau.prototype.log = function (message, force) {
    if (false && !force) {
        return;
    }

    console.log("****", message, "****");
    console.log("Nb Variables", this.width - 1);
    console.log("Nb Constraints", this.height - 1);
    // console.log("Variable Ids", this.variablesPerIndex);
    console.log("Basic Indexes", this.varIndexByRow);
    console.log("Non Basic Indexes", this.varIndexByCol);
    console.log("Rows", this.rowByVarIndex);
    console.log("Cols", this.colByVarIndex);

    var digitPrecision = 5;

    // Variable declaration
    var varNameRowString = "",
        spacePerColumn = [" "],
        j,
        c,
        s,
        r,
        variable,
        varIndex,
        varName,
        varNameLength,
        nSpaces,
        valueSpace,
        nameSpace;

    var row,
        rowString;

    for (c = 1; c < this.width; c += 1) {
        varIndex = this.varIndexByCol[c];
        variable = this.variablesPerIndex[varIndex];
        if (variable === undefined) {
            varName = "c" + varIndex;
        } else {
            varName = variable.id;
        }

        varNameLength = varName.length;
        nSpaces = Math.abs(varNameLength - 5);
        valueSpace = " ";
        nameSpace = "\t";

        ///////////
        /*valueSpace = " ";
        nameSpace = " ";

        for (s = 0; s < nSpaces; s += 1) {
            if (varNameLength > 5) {
                valueSpace += " ";
            } else {
                nameSpace += " ";
            }
        }*/

        ///////////
        if (varNameLength > 5) {
            valueSpace += " ";
        } else {
            nameSpace += "\t";
        }

        spacePerColumn[c] = valueSpace;

        varNameRowString += nameSpace + varName;
    }
    console.log(varNameRowString);

    var signSpace;

    // Displaying reduced costs
    var firstRow = this.matrix[this.costRowIndex];
    var firstRowString = "\t";

    ///////////
    /*for (j = 1; j < this.width; j += 1) {
        signSpace = firstRow[j] < 0 ? "" : " ";
        firstRowString += signSpace;
        firstRowString += spacePerColumn[j];
        firstRowString += firstRow[j].toFixed(2);
    }
    signSpace = firstRow[0] < 0 ? "" : " ";
    firstRowString += signSpace + spacePerColumn[0] +
        firstRow[0].toFixed(2);
    console.log(firstRowString + " Z");*/

    ///////////
    for (j = 1; j < this.width; j += 1) {
        signSpace = "\t";
        firstRowString += signSpace;
        firstRowString += spacePerColumn[j];
        firstRowString += firstRow[j].toFixed(digitPrecision);
    }
    signSpace = "\t";
    firstRowString += signSpace + spacePerColumn[0] +
        firstRow[0].toFixed(digitPrecision);
    console.log(firstRowString + "\tZ");


    // Then the basic variable rowByVarIndex
    for (r = 1; r < this.height; r += 1) {
        row = this.matrix[r];
        rowString = "\t";

        ///////////
        /*for (c = 1; c < this.width; c += 1) {
            signSpace = row[c] < 0 ? "" : " ";
            rowString += signSpace + spacePerColumn[c] + row[c].toFixed(2);
        }
        signSpace = row[0] < 0 ? "" : " ";
        rowString += signSpace + spacePerColumn[0] + row[0].toFixed(2);*/

        ///////////
        for (c = 1; c < this.width; c += 1) {
            signSpace = "\t";
            rowString += signSpace + spacePerColumn[c] + row[c].toFixed(digitPrecision);
        }
        signSpace = "\t";
        rowString += signSpace + spacePerColumn[0] + row[0].toFixed(digitPrecision);


        varIndex = this.varIndexByRow[r];
        variable = this.variablesPerIndex[varIndex];
        if (variable === undefined) {
            varName = "c" + varIndex;
        } else {
            varName = variable.id;
        }
        console.log(rowString + "\t" + varName);
    }
    console.log("");

    // Then reduced costs for optional objectives
    var nOptionalObjectives = this.optionalObjectives.length;
    if (nOptionalObjectives > 0) {
        console.log("    Optional objectives:");
        for (var o = 0; o < nOptionalObjectives; o += 1) {
            var reducedCosts = this.optionalObjectives[o].reducedCosts;
            var reducedCostsString = "";
            for (j = 1; j < this.width; j += 1) {
                signSpace = reducedCosts[j] < 0 ? "" : " ";
                reducedCostsString += signSpace;
                reducedCostsString += spacePerColumn[j];
                reducedCostsString += reducedCosts[j].toFixed(digitPrecision);
            }
            signSpace = reducedCosts[0] < 0 ? "" : " ";
            reducedCostsString += signSpace + spacePerColumn[0] +
                reducedCosts[0].toFixed(digitPrecision);
            console.log(reducedCostsString + " z" + o);
        }
    }
    console.log("Feasible?", this.feasible);
    console.log("evaluation", this.evaluation);

    return this;
};

Tableau.prototype.displayTableau = function () {
    var decNum = 4;
    var height = this.height;
    var width = this.width;
    var matrix = this.matrix;
    var basis = this.basis;
    var basisCosts = this.basisCosts;
    var i, j;
    var str = "z\t";
    console.log("##### full tableau #####");

    for (i = 1; i < width; i++) {
        str += "x" + this.varIndexByCol[i] + "\t";
    }
    str += "||\t";
    for (i = 1; i < height; i++) {
        str += "x" + this.varIndexByRow[i] + "\t";
    }
    console.log(str);
    for (i = 0; i < height; i++) {
        str = "";
        for (j = 0; j < width; j++) {
            str += matrix[i][j].toFixed(decNum) + "\t";
        }
        if (i === 0 && this.model.useRevisedSimplex) {
            str += "||\t";
            for (j = 0; j < this.height - 1; j++) {
                str += basisCosts[j].toFixed(decNum) + "\t";
            }
        } else if (this.model.useRevisedSimplex) {
            str += "||\t";
            for (j = 0; j < this.height - 1; j++) {
                str += basis[i - 1][j].toFixed(decNum) + "\t";
            }
        }
        console.log(str);
    }
    console.log("########################");
};

Tableau.prototype.displayMatrix = function (M, title) {
    var decNum = 4;
    console.log("#############", title, "beg #############");
    for (var i = 0; i < M.length; i++) {
        var str = "";
        for (var j = 0; j < M[0].length; j++) {
            str += M[i][j].toFixed(decNum) + "\t";
        }
        console.log(str);
    }
    console.log("#############", title, "end #############");
};

Tableau.prototype.debugLog = function (callback, debug) {
    if (debug) {
        callback();
    }
};

},{"./Tableau.js":7}],16:[function(require,module,exports){
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

    // console.log("matrix", JSON.stringify(this.matrix));

    while (true) {
        console.log("PHASE 1 ITERATION :", iterations);
        // console.log("rowByVarIndex", JSON.stringify(this.rowByVarIndex));
		// console.log("varIndexByRow", JSON.stringify(this.varIndexByRow));
		// console.log("unrestricted", JSON.stringify(this.unrestrictedVars));
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


        console.log(leavingRowIndex, enteringColumn);
        this.pivot(leavingRowIndex, enteringColumn);
        iterations += 1;

        // console.log("matrix", JSON.stringify(this.matrix));

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
        console.log("PHASE 2 ITERATION :", iterations);
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

        console.log(leavingRow, enteringColumn);
        this.pivot(leavingRow, enteringColumn, true);
        iterations += 1;

        // console.log("matrix", JSON.stringify(this.matrix));
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

},{"./LUDecomposition.js":4,"./Tableau.js":7}],17:[function(require,module,exports){
/*global describe*/
/*global require*/
/*global module*/
/*global it*/
/*global console*/
/*global process*/
/*global exports*/


// All functions in this module that
// get exported to main ***MUST***
// return a functional LPSolve JSON style
// model or throw an error

exports.CleanObjectiveAttributes = function(model){
  // Test to see if the objective attribute
  // is also used by one of the constraints
  //
  // If so...create a new attribute on each
  // variable
    var fakeAttr,
        x, z;
  
    if(typeof model.optimize === "string"){
        if(model.constraints[model.optimize]){
            // Create the new attribute
            fakeAttr = Math.random();

            // Go over each variable and check
            for(x in model.variables){
                // Is it there?
                if(model.variables[x][model.optimize]){
                    model.variables[x][fakeAttr] = model.variables[x][model.optimize];
                }
            }

        // Now that we've cleaned up the variables
        // we need to clean up the constraints
            model.constraints[fakeAttr] = model.constraints[model.optimize];
            delete model.constraints[model.optimize];
            return model;
        } else {    
            return model;
        }  
    } else {
        // We're assuming its an object?
        for(z in model.optimize){
            if(model.constraints[z]){
            // Make sure that the constraint
            // being optimized isn't constrained
            // by an equity collar
                if(model.constraints[z] === "equal"){
                    // Its constrained by an equal sign;
                    // delete that objective and move on
                    delete model.optimize[z];
                
                } else {
                    // Create the new attribute
                    fakeAttr = Math.random();

                    // Go over each variable and check
                    for(x in model.variables){
                        // Is it there?
                        if(model.variables[x][z]){
                            model.variables[x][fakeAttr] = model.variables[x][z];
                        }
                    }
                // Now that we've cleaned up the variables
                // we need to clean up the constraints
                    model.constraints[fakeAttr] = model.constraints[z];
                    delete model.constraints[z];            
                }
            }    
        }
        return model;
    }
};

},{}],18:[function(require,module,exports){
/*global describe*/
/*global require*/
/*global module*/
/*global it*/
/*global console*/
/*global process*/

//-------------------------------------------------------------------
//-------------------------------------------------------------------
function Variable(id, cost, index, priority) {
    this.id = id;
    this.cost = cost;
    this.index = index;
    this.value = 0;
    this.priority = priority;
}

function IntegerVariable(id, cost, index, priority) {
    Variable.call(this, id, cost, index, priority);
}
IntegerVariable.prototype.isInteger = true;

function SlackVariable(id, index) {
    Variable.call(this, id, 0, index, 0);
}
SlackVariable.prototype.isSlack = true;

//-------------------------------------------------------------------
//-------------------------------------------------------------------
function Term(variable, coefficient) {
    this.variable = variable;
    this.coefficient = coefficient;
}

function createRelaxationVariable(model, weight, priority) {
    if (priority === 0 || priority === "required") {
        return null;
    }

    weight = weight || 1;
    priority = priority || 1;

    if (model.isMinimization === false) {
        weight = -weight;
    }

    return model.addVariable(weight, "r" + (model.relaxationIndex++), false, false, priority);
}

//-------------------------------------------------------------------
//-------------------------------------------------------------------
function Constraint(rhs, isUpperBound, index, model) {
    this.slack = new SlackVariable("s" + index, index);
    this.index = index;
    this.model = model;
    this.rhs = rhs;
    this.isUpperBound = isUpperBound;

    this.terms = [];
    this.termsByVarIndex = {};

    // Error variable in case the constraint is relaxed
    this.relaxation = null;
}

Constraint.prototype.addTerm = function (coefficient, variable) {
    var varIndex = variable.index;
    var term = this.termsByVarIndex[varIndex];
    if (term === undefined) {
        // No term for given variable
        term = new Term(variable, coefficient);
        this.termsByVarIndex[varIndex] = term;
        this.terms.push(term);
        if (this.isUpperBound === true) {
            coefficient = -coefficient;
        }
        this.model.updateConstraintCoefficient(this, variable, coefficient);
    } else {
        // Term for given variable already exists
        // updating its coefficient
        var newCoefficient = term.coefficient + coefficient;
        this.setVariableCoefficient(newCoefficient, variable);
    }

    return this;
};

Constraint.prototype.removeTerm = function (term) {
    // TODO
    return this;
};

Constraint.prototype.setRightHandSide = function (newRhs) {
    if (newRhs !== this.rhs) {
        var difference = newRhs - this.rhs;
        if (this.isUpperBound === true) {
            difference = -difference;
        }

        this.rhs = newRhs;
        this.model.updateRightHandSide(this, difference);
    }

    return this;
};

Constraint.prototype.setVariableCoefficient = function (newCoefficient, variable) {
    var varIndex = variable.index;
    if (varIndex === -1) {
        console.warn("[Constraint.setVariableCoefficient] Trying to change coefficient of inexistant variable.");
        return;
    }

    var term = this.termsByVarIndex[varIndex];
    if (term === undefined) {
        // No term for given variable
        this.addTerm(newCoefficient, variable);
    } else {
        // Term for given variable already exists
        // updating its coefficient if changed
        if (newCoefficient !== term.coefficient) {
            var difference = newCoefficient - term.coefficient;
            if (this.isUpperBound === true) {
                difference = -difference;
            }

            term.coefficient = newCoefficient;
            this.model.updateConstraintCoefficient(this, variable, difference);
        }
    }

    return this;
};

Constraint.prototype.relax = function (weight, priority) {
    this.relaxation = createRelaxationVariable(this.model, weight, priority);
    this._relax(this.relaxation);
};

Constraint.prototype._relax = function (relaxationVariable) {
    if (relaxationVariable === null) {
        // Relaxation variable not created, priority was probably "required"
        return;
    }

    if (this.isUpperBound) {
        this.setVariableCoefficient(-1, relaxationVariable);
    } else {
        this.setVariableCoefficient(1, relaxationVariable);
    }
};

//-------------------------------------------------------------------
//-------------------------------------------------------------------
function Equality(constraintUpper, constraintLower) {
    this.upperBound = constraintUpper;
    this.lowerBound = constraintLower;
    this.model = constraintUpper.model;
    this.rhs = constraintUpper.rhs;
    this.relaxation = null;
}

Equality.prototype.isEquality = true;

Equality.prototype.addTerm = function (coefficient, variable) {
    this.upperBound.addTerm(coefficient, variable);
    this.lowerBound.addTerm(coefficient, variable);
    return this;
};

Equality.prototype.removeTerm = function (term) {
    this.upperBound.removeTerm(term);
    this.lowerBound.removeTerm(term);
    return this;
};

Equality.prototype.setRightHandSide = function (rhs) {
    this.upperBound.setRightHandSide(rhs);
    this.lowerBound.setRightHandSide(rhs);
    this.rhs = rhs;
};

Equality.prototype.relax = function (weight, priority) {
    this.relaxation = createRelaxationVariable(this.model, weight, priority);
    this.upperBound.relaxation = this.relaxation;
    this.upperBound._relax(this.relaxation);
    this.lowerBound.relaxation = this.relaxation;
    this.lowerBound._relax(this.relaxation);
};


module.exports = {
    Constraint: Constraint,
    Variable: Variable,
    IntegerVariable: IntegerVariable,
    SlackVariable: SlackVariable,
    Equality: Equality,
    Term: Term
};

},{}],19:[function(require,module,exports){
/*global describe*/
/*global require*/
/*global module*/
/*global it*/
/*global console*/
/*global process*/


//-------------------------------------------------------------------
// SimplexJS
// https://github.com/
// An Object-Oriented Linear Programming Solver
//
// By Justin Wolcott (c)
// Licensed under the MIT License.
//-------------------------------------------------------------------

var Tableau = require("./Tableau/index.js");
var Model = require("./Model");
var branchAndCut = require("./Tableau/branchAndCut");
var expressions = require("./expressions.js");
var validation = require("./Validation");
var Constraint = expressions.Constraint;
var Variable = expressions.Variable;
var Numeral = expressions.Numeral;
var Term = expressions.Term;

// Place everything under the Solver Name Space
var Solver = function () {

    "use strict";

    this.Model = Model;
    this.branchAndCut = branchAndCut;
    this.Constraint = Constraint;
    this.Variable = Variable;
    this.Numeral = Numeral;
    this.Term = Term;
    this.Tableau = Tableau;

    this.lastSolvedModel = null;

    /*************************************************************
     * Method: Solve
     * Scope: Public:
     * Arguments:
     *        model: The model we want solver to operate on
     *        precision: If we're solving a MILP, how tight
     *                   do we want to define an integer, given
     *                   that 20.000000000000001 is not an integer.
     *                   (defaults to 1e-9)
     *            full: *get better description*
     *        validate: if left blank, it will get ignored; otherwise
     *                  it will run the model through all validation
     *                  functions in the *Validate* module
     *        activateMIRCuts: set to true to activate the MIR cuts
     *        debug: set to true to enable cycle detection
     **************************************************************/
    this.Solve = function (model, precision, full, validate, activateRevisedSimplex, activateMIRCuts, debug) {
    // this.Solve = function (model, precision, full, validate) {
        // Run our validations on the model
        // if the model doesn't have a validate
        // attribute set to false
        if(validate){
            for(var test in validation){
                model = validation[test](model);
            }
        }

        // Make sure we at least have a model
        if (!model) {
            throw new Error("Solver requires a model to operate on");
        }

        if (model instanceof Model === false) {
            var m = new Model(precision);

            if (typeof activateRevisedSimplex === "undefined") {
                m.activateRevisedSimplex(false);
            }
            else {
                m.activateRevisedSimplex(activateRevisedSimplex);
            }

            if (typeof activateMIRCuts === "undefined") {
                m.activateMIRCuts(false);
            }
            else {
                m.activateMIRCuts(activateMIRCuts);
            }

            if (typeof debug === "undefined") {
                m.debug(false);
            }
            else {
                m.debug(debug);
            }

            model = m.loadJson(model);
        }

        var solution = model.solve();
        this.lastSolvedModel = model;
        solution.solutionSet = solution.generateSolutionSet();

        // If the user asks for a full breakdown
        // of the tableau (e.g. full === true)
        // this will return it
        if (full) {
            return solution;
        } else {
            // Otherwise; give the user the bare
            // minimum of info necessary to carry on

            var store = {};

            // 1.) Add in feasibility to store;
            store.feasible = solution.feasible;

            // 2.) Add in the objective value
            store.result = solution.evaluation;

            store.bounded = solution.bounded;

            // 3.) Load all of the variable values
            Object.keys(solution.solutionSet)
                .map(function (d) {
                    store[d] = solution.solutionSet[d];
                });

            return store;
        }

    };

    /*************************************************************
     * Method: ReformatLP
     * Scope: Public:
     * Agruments: model: The model we want solver to operate on
     * Purpose: Convert a friendly JSON model into a model for a
     *          real solving library...in this case
     *          lp_solver
     **************************************************************/
    this.ReformatLP = require("./Reformat");


     /*************************************************************
     * Method: MultiObjective
     * Scope: Public:
     * Agruments:
     *        model: The model we want solver to operate on
     *        detail: if false, or undefined; it will return the
     *                result of using the mid-point formula; otherwise
     *                it will return an object containing:
     *
     *                1. The results from the mid point formula
     *                2. The solution for each objective solved
     *                   in isolation (pareto)
     *                3. The min and max of each variable along
     *                   the frontier of the polytope (ranges)
     * Purpose: Solve a model with multiple objective functions.
     *          Since a potential infinite number of solutions exist
     *          this naively returns the mid-point between
     *
     * Note: The model has to be changed a little to work with this.
     *       Before an *opType* was required. No more. The objective
     *       attribute of the model is now an object instead of a
     *       string.
     *
     *  *EXAMPLE MODEL*
     *
     *   model = {
     *       optimize: {scotch: "max", soda: "max"},
     *       constraints: {fluid: {equal: 100}},
     *       variables: {
     *           scotch: {fluid: 1, scotch: 1},
     *           soda: {fluid: 1, soda: 1}
     *       }
     *   }
     *
     **************************************************************/
    this.MultiObjective = function(model){
        return require("./Polyopt")(this, model);
    };
};

// Determine the environment we're in.
// if we're in node, offer a friendly exports
// otherwise, Solver's going global
/* jshint ignore:start */

(function(){
    // If define exists; use it
    if (typeof define === "function") {
        define([], function () {
            return new Solver();
        });
    } else if(typeof window === "object"){
        window.solver = new Solver();
    } else {
        module.exports =  new Solver();
    }
})()

/* jshint ignore:end */

},{"./Model":1,"./Polyopt":2,"./Reformat":3,"./Tableau/branchAndCut":9,"./Tableau/index.js":13,"./Validation":17,"./expressions.js":18}]},{},[19]);
