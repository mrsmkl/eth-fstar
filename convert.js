
var fs = require("fs")
var conv = require("./tofstar")

var compileJSON = require("./soljson").cwrap('compileJSON', 'string', ['string', 'number']);

console.log()

function compile() {
    if (process.argv.length < 3) {
        console.err("Input file name")
        return
    }
    var fname = process.argv[2]
    var str = fs.readFileSync(fname).toString()
    // 
    var dta = JSON.parse(compileJSON(str))
    var converted = conv.convertUnit(dta.sources[''].AST)
    fs.writeFileSync(fname.replace(/\.sol/, ".fst"), converted)
}


compile()
