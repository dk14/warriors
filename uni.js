function inferMembound(turing) {
    const base = turing.filter(x => x[1] !== 0n && x[1] < TURING_OFFSET).length
    return {
        currentExpansion: base,
        currentHyperop: 0n,
        hyperopBound: turing.filter(x => x[1] > TURING_OFFSET).length,
        baseBound: base,
    }

}

function powBigInt(base, exponent) {
    base = BigInt(base);
    exponent = BigInt(exponent);
    if (exponent < 0n) throw new RangeError('negative exponent not supported for BigInt');
    let result = 1n;
    while (exponent > 0n) {
        if (exponent & 1n) result *= base;
        base *= base;
        exponent >>= 1n;
    }
    return result;
}

function checkMembound(value, membound) {

    let counter = 0n
    while (membound.currentExpansion < value && membound.currentHyperop < membound.hyperopBound) {
        counter++
        if (counter > 30n) {
            console.log(membound)
            throw "check mem overflow"
        }
        membound.currentExpansion = powBigInt(membound.currentExpansion, membound.baseBound)
        membound.currentHyperop++
    }

    return membound.currentExpansion >= value

}

function minBigInt(arr) {
    if (arr.length === 0) return undefined
    return arr.reduce((a, b) => (a < b ? a : b));
}

function maxBigInt(arr) {
    if (arr.length === 0) return undefined
    return arr.reduce((a, b) => (a > b ? a : b));
}

const getJumpDestination = jump => jump[1] - TURING_OFFSET

const createJumpDestination = cur => cur + TURING_OFFSET

const getLoopVar = jump => jump[0]

const filterCov = (coverage, start, end) => new Set([...coverage].filter(x => x >= start && x <= end))

function checkLoopSegment(turing, coverage, jump, cursor, memory, lastLoopVarState, lastCov) {

    if (!lastLoopVarState || !lastCov) return true
    const loopStart = getJumpDestination(jump)
    const loopEnd = cursor
    if (loopStart > loopEnd) return true

    const loopVarIdx = getLoopVar(jump)
    const loopVar = memory[loopVarIdx]

    const segmentJumps = turing.slice(Number(loopStart), Number(loopEnd)).map(getJumpDestination).filter(x => x >= 0n)
    const minDest = minBigInt(segmentJumps)
    const maxDest = maxBigInt(segmentJumps) > loopEnd ? BigInt(turing.length-1) : loopEnd
    //todo improve up to any instruction that jumps above loopEnd

    const expandedStart = minDest === undefined ? loopStart : minBigInt([loopStart, minDest])
    const expandedEnd = maxDest === undefined ? loopEnd : maxBigInt([loopStart, maxDest])

    //todo check if expanded segment refers to variables in current segment

    //todo check if dec extruction mentioned for loopvar at all

    //todo exclude unreachable segments - no dec instruction for forward jmp
    
    const segmentCov = filterCov(coverage, expandedStart, expandedEnd)
    const segmentLastCov = filterCov(coverage, expandedStart, expandedEnd)


    if (BigInt(segmentCov.size) >= expandedEnd - expandedStart && loopVar >= lastLoopVarState && loopVar !== 0n) {
        return false
    }

    return true
}

function bigIntArraysEqual(a, b) {
    if (a.length !== b.length) return false;
    for (let i = 0; i < a.length; i++) {
        if (a[i] !== b[i]) return false; // BigInt compared with ===
    }
    return true;
}

function checkRepeatCfg(state, cursor, history) {
    for (const x of history){
        const [pastCursor, pastState] = x
        if (pastCursor === cursor && bigIntArraysEqual(pastState, state)) {
            return false
        }
    }
    return true
}

const TURING_INC = 2n
const TURING_DEC = 1n
const TURING_OUT = 0n
const TURING_OFFSET = 100n

const TURING_JMP = (instrPointer) => instrPointer + TURING_OFFSET

//input is sequence of [mem_address, instr_address]
//instr_address past offset jmpnz mem_address (instr_address - offset)
//other instr_address as inc dec out
function executeTuring(turing, ctx = {}) {

    ctx.trace = []
    ctx.membound = inferMembound(turing)
    const membound = ctx.membound

    let cursor = 0n

    ctx.memory = []
    const memory = ctx.memory

    const output = []

    ctx.history = []
    const history = ctx.history

    ctx.coverage = new Set()
    const coverage = ctx.coverage

    const lastCoverageForJmp = {}
    const lastLoopVarStateForJmp = {}

    let safeCounter = 0n

    while (cursor < turing.length) {
        ctx.trace.push(cursor)
        safeCounter++
        if (safeCounter > 3000n) {
            console.log(ctx)
            console.log(printTuring(turing))
            throw "overflow " + cursor
        }

        const [mem, instr] = turing[cursor]

        if (instr === TURING_OUT) {
            output.push(mem)
            coverage.add(cursor)
            cursor++
        } else if (instr === TURING_INC) {
            if (memory[mem] === undefined) memory[mem] = 0n
            memory[mem]++
            if(!checkMembound(memory[mem], membound)) {

                const loopJmp = turing.findLastIndex(x => x[1] >= TURING_OFFSET + BigInt(turing.length))
                
                const noOuterJumps = loopJmp !== -1 && !turing.slice(loopJmp).some(x => x[1] > TURING_OFFSET && x[1] < TURING_OFFSET + BigInt(loopJmp))
                if (noOuterJumps) {
                    memory[turing[loopJmp][0]] = mem
                    cursor = loopJmp
                } else {
                    console.log("LOOP HYPER: " + cursor)
                    ctx.loopHyper = cursor
                    ctx.loopState = memory[mem]
                    return output
                }
                
            } else {
                coverage.add(cursor)
                cursor++
            }
            
        } else if (instr === TURING_DEC) {
            if (memory[mem] === undefined) memory[mem] = 0n
            memory[mem]--
            if (memory[mem] < 0n) memory[mem] = 0n
            coverage.add(cursor)
            cursor++
        } else {
            if (memory[mem] === undefined) memory[mem] = 0n
            if (memory[mem] === 0n) {
                cursor++
            } else {

                const nextCursorShift = turing.slice(Number(cursor) + 1).findIndex(x => x[1] !== TURING_OUT)
                const nextCursor = nextCursorShift === -1 ? turing.length + 1 : cursor + BigInt(nextCursorShift) + 1n
                coverage.add(cursor)
                const lastCov = lastCoverageForJmp[cursor.toString]
                const lastLoopVarState = lastLoopVarStateForJmp[cursor.toString]
                const nonTerminationRecovery = turing[nextCursor] && turing[nextCursor][1] - TURING_OFFSET !== cursor && turing[nextCursor][1] > TURING_OFFSET && turing[nextCursor][0] === mem //for theorem provers

                if (!checkLoopSegment(turing, coverage, turing[cursor], cursor, memory, lastLoopVarState, lastCov)) {
                    if (nonTerminationRecovery) {
                        cursor = nextCursor
                    } else {
                        console.log("LOOP SEG: " + cursor)
                        ctx.loopSegment = cursor
                        return output
                    }  
                } else {
                    cursor = instr - TURING_OFFSET
                    if (!checkRepeatCfg(memory, cursor, history)) {
                    
                        if (nonTerminationRecovery) {
                            cursor = nextCursor
                        } else {
                            console.log("LOOP REPEAT: " + cursor)
                            ctx.loopRepeat = cursor
                            return output
                        }
                    }
                    lastCoverageForJmp[cursor.toString] = coverage
                    lastLoopVarStateForJmp[cursor.toString] = memory[mem]

                }
                
            }
        }
        
    }

    return output
}

function genJump(turing, varIdx, label) {
    const outs = turing
        .map((x,i) => [x[0], x[1], BigInt(i)])
        .filter(x => x[1] === 0n)
        .map(x => [x[0], x[2]]) //char, line_no

        
    const instrPointer = find(outs, label)[0] //take first label
    if (instrPointer === undefined) {
        return undefined
    }
    return [varIdx, instrPointer[1] + TURING_OFFSET]
}

function genStubJmp(turing, varIdx) {
    return [varIdx, BigInt(turing.length) + TURING_OFFSET + 1n]
}


function genInc(varIdx) {
    return [varIdx, TURING_INC]
}

function genDec(varIdx) {
    return [varIdx, TURING_DEC]
}

function genOut(next) {
    return [next[0], 0n]
}

function printTuring(turing, parseOut=true) {
    return turing.map((x, i) => {
        if (x[1] === TURING_INC) {
            return `${i}: inc \$${x[0]}`
        } else if (x[1] === TURING_DEC) {
            return `${i}: dec \$${x[0]}`
        } else if (x[1] === TURING_OUT) {
            return `${i}: out ${parseOut ? parse([[x[0], 0]]):x[0]}`
        } else {
            return `${i}: jmp \$${x[0]} -> ${getJumpDestination(x)}`
        }
    }).join("\n")
}

const ctxTuring = {}
const program = [
    [0n,   TURING_INC], 
    [0n,   TURING_JMP(0n)], 
    [0n,   TURING_JMP(4n)], 
    [20n,  TURING_OUT],
    [-1n,   TURING_OUT], 
    [0n,   TURING_INC], 
]

const program2 = [
    [0n,   TURING_INC], 
    [0n,   TURING_JMP(0n)], 
    [0n,  TURING_OUT],
    [0n,   TURING_JMP(100n)], 
    [-1n,   TURING_OUT], 
]

console.log("\n\nTURING TEST")

console.log(printTuring(program, false))

const output = executeTuring(program, ctxTuring)

console.log("TURING OUT: " + output)

console.log(ctxTuring)

console.log("TURING END\n\n\n")



const am0 = {
    radix: 0n,
    membound: 0n,
    instrbound: 0n,
    inputLengthBound: 0n,
    inputCellBound: 0n,
    input: [],
    machine: []

}

const nextInput = (input, bound) => {

}

const genInputAndMachine = (am) => {

}

const nextAm = (am) => {
    am.membound++
    if (am.membound < am.radix) {     
        return genInputAndMachine(am)
    }
    am.membound = 0n

    am.instrbound++
    if (am.instrbound < am.radix) {    
        return genInputAndMachine(am)
    }
    am.instrbound = 0n

    am.inputLengthBound++
    if (am.inputLengthBound < am.radix) {
        return genInputAndMachine(am)
    }
    am.inputLengthBound = 0n

    am.inputCellBound++
    if (am.inputCellBound < am.radix) { 
        return genInputAndMachine(am)
    }
    am.inputCellBound = 0n

    am.radix++
    return genInputAndMachine(am)

}