
var get_file = function (yourUrl){
    var req = new XMLHttpRequest(); // a new request
    req.open("GET",yourUrl,false);
    req.send(null);
    return req.responseText;          
}

if (typeof exports != "undefined") {
    var fs = require("fs")
    get_file = x => fs.readFileSync(x)
}

var preamble = get_file("Preamble.fst")

var convert = {}

var type_table = {
    uint: "UInt256.t",
    uint256: "UInt256.t",
    address: "UInt160.t",
    bool: "bool",
    bytes32: "UInt256.t"
}

function doConvert(part) {
    if (convert[part.name]) return convert[part.name](part)
    console.log(part.name)
    console.log(part)
    return ""
}

convert.ElementaryTypeName = function (m) {
    return type_table[m.attributes.name]
}

convert.UserDefinedTypeName = function (m) {
    return "struct_" + m.attributes.name
}

convert.ArrayTypeName = function (m) {
    return "list (" + doConvert(m.children[0]) + ")"
}

convert.Mapping = function (m) {
    return doConvert(m.children[0]) + " -> " + doConvert(m.children[1])
}

convert.IfStatement = function (a) {
    var str = ""
    str += "if " + doConvert(a.children[0]) + "\n"
    str += "then (" + doConvert(a.children[1]) + " ())\n"
    str += "else (" + (a.children[2] ? doConvert(a.children[2]) + " ()" : "") + ");\n"
    return str
}

convert.ExpressionStatement = function (a) {
    return doConvert(a.children[0]) + ";"
}

convert.Block = function (b) {
    return b.children.map(doConvert).join("\n")
}

convert.Return = function (a) {
    return "ret := Some("  + doConvert(a.children[0]) + "); raise SolidityReturn;"
}

convert.Literal = function (a) {
    if (a.attributes.type2 == "address") {
        return "address_" + a.attributes.value
    }
    if (a.attributes.type2 == "uint256") {
        return "uint256_" + a.attributes.value
    }
    if (a.attributes.type.match(/int_const/)) {
        return "uint256_" + a.attributes.value
    }
    if (a.attributes.type == "bool") {
        return a.attributes.value
    }
    console.log("Literal " + a.attributes.type)
    console.log(a)
}

var lits = {}

function prepareLiteral(a) {
    var name, type
    if (a.attributes.type2 == "address") {
        name = "address_" +  a.attributes.value
        type = "UInt160.uint_to_t"
    }
    else if (a.attributes.type2 == "uint256") {
        name = "uint256_" +  a.attributes.value
        type = "UInt256.uint_to_t"
    }
    else if (a.attributes.type.match(/int_const/)) {
        name = "uint256_" +  a.attributes.value
        type = "UInt256.uint_to_t"
    }
    else if (a.attributes.type == "bool") {
        return ""
    }
    else {
        console.log("Literal " + a.attributes.type)
        console.log(a)
    }
    if (lits[name]) return ""
    lits[name] = true
    return "let " + name + " = " + type + " (" + a.attributes.value + ")"
}

convert.Throw = function () {
    return "raise SolidityThrow;"
}

convert.PragmaDirective = function (a) {
}

convert.ForStatement = function (a) {
    var str = ""
    str += doConvert(a.children[0])
    str += "let rec loop_"+a.id+" () : ML unit =\n"
    str += "if not (" + doConvert(a.children[1]) + ") then () else (\n"
    str += doConvert(a.children[3])
    str += doConvert(a.children[2])
    str += "loop_" + a.id + " ()) in loop_"+a.id+"();"
    return str
}

convert.WhileStatement = function (a) {
    var str = ""
    str += "let rec loop_"+a.id+" () : ML unit =\n"
    str += "if not (" + doConvert(a.children[0]) + ") then () else (\n"
    str += doConvert(a.children[1])
    str += "loop_" + a.id + " ()) in loop_"+a.id+"();"
    return str
}

convert.Identifier = a => {
    // console.log(a);
    if (a.attributes.scope == "local") return "!" + a.attributes.value
    else if (a.attributes.scope == "param") return a.attributes.value
    return "(!s)." + a.attributes.value 
}

convert.IndexAccess = function (a) {
    console.log(a)
    if (a.children[0].attributes.type.match(/\[\] (storage ref|memory)/)) {
        return "(list_nth (" + doConvert(a.children[0]) + ") (" + doConvert(a.children[1]) + "))"
    }
    return "(get " + doConvert(a.children[0]) + " (" + doConvert(a.children[1]) + "))"
}

convert.MemberAccess = function (a) {
    if (a.attributes.member_name == "length") {
        return "list_length " + "(" + doConvert(a.children[0]) + ")"
    }
    return "(" + doConvert(a.children[0]) + ")." + a.attributes.member_name
}

var op_table = {
    "uint256 +=": "UInt256.add_mod",
    "uint256 -=": "UInt256.sub_mod",
    "uint256 +": "UInt256.add_mod",
    "uint256 -": "UInt256.sub_mod",
    "uint256 <": "UInt256.lt",
    "uint256 >": "UInt256.gt",
    
    "uint8 +=": "UInt8.add_mod",
    "uint8 -=": "UInt8.sub_mod",
    "uint8 +": "UInt8.add_mod",
    "uint8 -": "UInt8.sub_mod",
    "uint8 <": "UInt8.lt",
    "uint8 >": "UInt8.gt",
    
    "uint +=": "UInt256.add_mod",
    "uint -=": "UInt256.sub_mod",
    "uint +": "UInt256.add_mod",
    "uint -": "UInt256.sub_mod",
    "uint <": "UInt256.lt",
    "bool &&": "bool_and",
    "bool ||": "bool_or",
    "uint256 !=": "op_disEquality",
    "address !=": "op_disEquality",
    "address ==": "op_Equality",
}

function get_op(b) {
    var a = b.children[0]
    var op = op_table[a.attributes.type + " " + b.attributes.operator]
    if (!op) console.log(a.attributes.type + " " + b.attributes.operator)
    return op
}

function makeSetter(a, expr) {

    if (a.name == "MemberAccess") {
        var str = ""
        var c = a
        if (c.children[0].name == "IndexAccess") {
            var b = c.children[0]
            str += "let base = " + doConvert(b) + "in\n"
            str += "let base = {base with " + a.attributes.member_name + " = (" + expr + ") } in\n"
            str += makeSetter(b, "base")
            return str
        }
        if (c.children[0].name == "Identifier" && c.children[0].attributes.scope == "local") {
            var id = c.children[0].attributes.value
            return id + " := { !" + id + " with " + a.attributes.member_name + " = " + expr + " }"
        }
    
    }

    if (a.name == "IndexAccess") {
        if (a.children[0].attributes.type.match(/\[\] (storage ref|memory)/)) {
            return "s := {!s with " + a.children[0].attributes.value + " = list_set (" + doConvert(a.children[0]) + ") (" + doConvert(a.children[1]) + ") (" + expr + ") }"
        }
        return "s := {!s with " + a.children[0].attributes.value + " = set " + doConvert(a.children[0]) + " (" + doConvert(a.children[1]) + ") (" + expr + ") }"
    }

    if (a.name == "Identifier" && a.attributes.scope == "local") {
        return a.attributes.value + " := " + expr
    }
    
    if (a.name == "Identifier") {
        return "s := {!s with " + a.attributes.value + " = (" + expr + ") }"
    }
    
    console.log("setter")
    console.log(a)
}



convert.Assignment = function (a) {
    var v

    if (a.attributes.operator == "=") v = doConvert(a.children[1])
    else v = get_op(a) + " (" + doConvert(a.children[0]) + ") (" + doConvert(a.children[1]) + ")"
    
    return makeSetter(a.children[0], v)

}

convert.BinaryOperation = function (a) {
    return get_op(a) + " (" + doConvert(a.children[0]) + ") (" + doConvert(a.children[1]) + ")"
}

convert.UnaryOperation = function (a) {
    return get_op(a) + " (" + doConvert(a.children[0]) + ")"
}

function convertType(v) {
    return doConvert(v.children[0])
}

function guessType(str) {
    if (str.match(/int_const/)) return "uint256"
    else return str
}

var conversion = {
    "address uint256": "uint_to_address"
}


convert.FunctionCall = function (a) {
    if (a.children[0].attributes.member_name == "transfer") {
        return "()"
    }
    if (a.children[0].name == "ElementaryTypeNameExpression") {
        var t = a.children[0].attributes.value + " " + guessType(a.children[1].attributes.type)
        return conversion[t] + " " + doConvert(a.children[1])
    }
    if (a.children[0].name == "Identifier") {
        console.log(a)
        var str = ""
        str += "let (ret,st) = method_" + a.children[0].attributes.value + " msg !s\n"
        if (a.children.length == 1) str += "()"
        else for (var i = 1; i < a.children.length; i++) {
            str += doConvert(a.children[i])
        }
        str += " in\n (s := st; match ret with Some x -> x | None -> (* assert False ; *) raise SolidityBadReturn)"
        return str
    }
    if (a.children[0].attributes.member_name == "push") {
        // Expression representing array
        var target = a.children[0].children[0]
        var getter = doConvert(target)
        return makeSetter(target, getter + " @ [ " + doConvert(a.children[1]) + "]")
    }
    console.log(a)
}

function flatten(lst) {
    var res = []
    lst.forEach(a => res = res.concat(a))
    return res
}

function getChildren(a) {
    if (!a.children) return []
    return a.children.concat(flatten(a.children.map(b => getChildren(b))))
}

function checkTypes(a) {
    var a1 = a.children[0]
    var a2 = a.children[1]
    if (a1.attributes.type.match(/int_const/)) {
        a1.attributes.type2 = a2.attributes.type
    }
    if (a2.attributes.type.match(/int_const/)) {
        a2.attributes.type2 = a1.attributes.type
    }
}

convert.VariableDeclarationStatement = function (a) {
    return "let " + a.children[0].attributes.name + " = alloc (" + doConvert(a.children[1]) + ") in\n"
}

function convertArgTypes(lst) {
    if (lst.children.length == 0) return "unit"
    return lst.children.map(convertType).join(" -> ")
}

function convertRetTypes(lst) {
    if (lst.children.length == 0) return "unit"
    return lst.children.map(convertType).join(" * ")
}

function convertParams(lst) {
    if (lst.children.length == 0) return "()"
    return lst.children.map(a => a.attributes.name).join(" ")
}

convert.FunctionDefinition = function (a) {
    var str = ""
    // generate type
    str += "val method_" + a.attributes.name + " : msg -> state -> " + convertArgTypes(a.children[0]) + " -> ML (option (" + convertRetTypes(a.children[1]) + ") * state)\n"
    // generate body
    str += "let method_" + a.attributes.name + " msg state " + convertParams(a.children[0]) + " =\n"
    str += "let s = alloc state in\n"
    str += "let ret = alloc None in\n"
    // Find all declared variables here, set them to local variable
    var table = {}
    table["msg"] = "param"
    var children = getChildren(a.children[2])
    getChildren(a.children[2]).filter(a => a.name == "VariableDeclaration").forEach(a => table[a.attributes.name] = "local")
    a.children[0].children.forEach(a => table[a.attributes.name] = "param")
    getChildren(a.children[2]).filter(a => a.name == "Identifier").forEach(a => a.attributes.scope = table[a.attributes.value])
    str += "try\n"
    str += doConvert(a.children[2]) + "\n"
    str += "(!ret, !s)\n"
    str += "with SolidityReturn -> (!ret, !s)\n"
    return str
}

function convertVar(v) {
    return v.attributes.name + " : " + doConvert(v.children[0]) + ";"
}

function makeStruct(a) {
    var vars = a.children.filter(a => a.name == "VariableDeclaration")
    return "noeq type struct_" + a.attributes.name + " = {\n" + vars.map(convertVar).join("\n") + "\n}\n"
}

function makeStructConstructor(a) {
    var vars = a.children.filter(a => a.name == "VariableDeclaration")
    var str = ""
    str += "val method_" + a.attributes.name + " : msg -> state -> " + vars.map(a => convertType(a)).join(" -> ") + " -> ML (option (struct_" + a.attributes.name + ") * state)\n"
    // generate body
    str += "let method_" + a.attributes.name + " msg state " + vars.map(a => a.attributes.name).join(" ") + " = (Some ({\n"
    vars.forEach(a => str += "  " + a.attributes.name + " = " + a.attributes.name + ";\n")
    str += "}), state)\n"
    return str
}

convert.ContractDefinition = function (c) {
    // console.log(c)
    getChildren(c).filter(a => a.name == "BinaryOperation" || a.name == "Assignment").forEach(checkTypes)
    var str = ""
    str += "module " + c.attributes.name + "\n" + preamble
    // structs
    c.children.filter(a => a.name == "StructDefinition").forEach(a => str += makeStruct(a))
    // find variables
    var vars = c.children.filter(a => a.name == "VariableDeclaration")
    str += "\n\n\n(* Storage state *)\n"
    str += "noeq type state = {\n" + vars.map(convertVar).join("\n") + "\n}\n"
    c.children.filter(a => a.name == "StructDefinition").forEach(a => str += makeStructConstructor(a))
    // literals
    getChildren(c).filter(a => a.name == "Literal").forEach(l => str += prepareLiteral(l) + "\n")
    // find methods
    var lst = c.children.filter(a => a.name == "FunctionDefinition")
    str += "\n\n\n(* Contract methods *)\n"
    str += lst.map(doConvert).join("\n\n")
    return str
}

function convertUnit(unit) {
    if (!unit.children) return ""
    var lst = unit.children.map(doConvert)
    return lst.join("\n(******************)\n")
}

if (typeof exports != "undefined") exports.convertUnit = convertUnit

