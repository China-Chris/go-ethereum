// Copyright 2017 The go-ethereum Authors
// This file is part of go-ethereum.
//
// go-ethereum is free software: you can redistribute it and/or modify
// it under the terms of the GNU General Public License as published by
// the Free Software Foundation, either version 3 of the License, or
// (at your option) any later version.
//
// go-ethereum is distributed in the hope that it will be useful,
// but WITHOUT ANY WARRANTY; without even the implied warranty of
// MERCHANTABILITY or FITNESS FOR A PARTICULAR PURPOSE. See the
// GNU General Public License for more details.
//
// You should have received a copy of the GNU General Public License
// along with go-ethereum. If not, see <http://www.gnu.org/licenses/>.

package main

import (
	"bytes"
	"encoding/json"
	"fmt"
	"io"
	"math/big"
	"os"
	goruntime "runtime"
	"testing"
	"time"

	"github.com/ethereum/go-ethereum/cmd/evm/internal/compiler"
	"github.com/ethereum/go-ethereum/cmd/utils"
	"github.com/ethereum/go-ethereum/common"
	"github.com/ethereum/go-ethereum/core"
	"github.com/ethereum/go-ethereum/core/rawdb"
	"github.com/ethereum/go-ethereum/core/state"
	"github.com/ethereum/go-ethereum/core/vm"
	"github.com/ethereum/go-ethereum/core/vm/runtime"
	"github.com/ethereum/go-ethereum/eth/tracers/logger"
	"github.com/ethereum/go-ethereum/internal/flags"
	"github.com/ethereum/go-ethereum/params"
	"github.com/ethereum/go-ethereum/trie"
	"github.com/ethereum/go-ethereum/trie/triedb/hashdb"
	"github.com/urfave/cli/v2"
)

var runCommand = &cli.Command{
	Action:      runCmd,
	Name:        "run",
	Usage:       "Run arbitrary evm binary",
	ArgsUsage:   "<code>",
	Description: `The run command runs arbitrary EVM code.`,
	Flags:       flags.Merge(vmFlags, traceFlags),
}

// readGenesis will read the given JSON format genesis file and return
// the initialized Genesis structure
func readGenesis(genesisPath string) *core.Genesis {
	// Make sure we have a valid genesis JSON
	//genesisPath := ctx.Args().First()
	if len(genesisPath) == 0 {
		utils.Fatalf("Must supply path to genesis JSON file")
	}
	file, err := os.Open(genesisPath)
	if err != nil {
		utils.Fatalf("Failed to read genesis file: %v", err)
	}
	defer file.Close()

	genesis := new(core.Genesis)
	if err := json.NewDecoder(file).Decode(genesis); err != nil {
		utils.Fatalf("invalid genesis file: %v", err)
	}
	return genesis
}

type execStats struct {
	time           time.Duration // The execution time.
	allocs         int64         // The number of heap allocations during execution.
	bytesAllocated int64         // The cumulative number of bytes allocated during execution.
}

func timedExec(bench bool, execFunc func() ([]byte, uint64, error)) (output []byte, gasLeft uint64, stats execStats, err error) {
	if bench {
		result := testing.Benchmark(func(b *testing.B) {
			for i := 0; i < b.N; i++ {
				output, gasLeft, err = execFunc()
			}
		})

		// Get the average execution time from the benchmarking result.
		// There are other useful stats here that could be reported.
		stats.time = time.Duration(result.NsPerOp())
		stats.allocs = result.AllocsPerOp()
		stats.bytesAllocated = result.AllocedBytesPerOp()
	} else {
		var memStatsBefore, memStatsAfter goruntime.MemStats
		goruntime.ReadMemStats(&memStatsBefore)
		startTime := time.Now()
		output, gasLeft, err = execFunc()
		stats.time = time.Since(startTime)
		goruntime.ReadMemStats(&memStatsAfter)
		stats.allocs = int64(memStatsAfter.Mallocs - memStatsBefore.Mallocs)
		stats.bytesAllocated = int64(memStatsAfter.TotalAlloc - memStatsBefore.TotalAlloc)
	}

	return output, gasLeft, stats, err
}

func runCmd(ctx *cli.Context) error { //runCmd函数 是evm命令的入口函数
	logconfig := &logger.Config{ //logconfig是日志配置
		EnableMemory:     !ctx.Bool(DisableMemoryFlag.Name),     //EnableMemory   是否启用Memory  默认为true Memory(内存)
		DisableStack:     ctx.Bool(DisableStackFlag.Name),       //DisableStack   是否禁用Stack  默认为false Stack(堆栈)
		DisableStorage:   ctx.Bool(DisableStorageFlag.Name),     //DisableStorage 是否禁用Storage 默认为false Storage(存储)
		EnableReturnData: !ctx.Bool(DisableReturnDataFlag.Name), //EnableReturnData 是否启用ReturnData 默认为true ReturnData(返回数据)
		Debug:            ctx.Bool(DebugFlag.Name),              //Debug 是否启用Debug 默认为false
	}

	var (
		tracer      vm.EVMLogger                                //tracer是虚拟机的日志
		debugLogger *logger.StructLogger                        //debugLogger是日志结构体
		statedb     *state.StateDB                              //statedb是状态数据库
		chainConfig *params.ChainConfig                         //chainConfig是链配置
		sender      = common.BytesToAddress([]byte("sender"))   //sender是发送者
		receiver    = common.BytesToAddress([]byte("receiver")) //receiver是接收者
		preimages   = ctx.Bool(DumpFlag.Name)                   //preimages是预映像
		blobHashes  []common.Hash                               // TODO (MariusVanDerWijden) implement blob hashes in state tests
		blobBaseFee = new(big.Int)                              // TODO (MariusVanDerWijden) implement blob fee in state tests
	)
	if ctx.Bool(MachineFlag.Name) { //MachineFlag.Name = "machine"  MachineFlag.Usage = "use the new EVM execution model"
		tracer = logger.NewJSONLogger(logconfig, os.Stdout) //tracer是虚拟机的日志
	} else if ctx.Bool(DebugFlag.Name) { //DebugFlag.Name = "debug"  DebugFlag.Usage = "enable debug logging"
		debugLogger = logger.NewStructLogger(logconfig) //debugLogger是日志结构体
		tracer = debugLogger                            //tracer是虚拟机的日志
	} else { //如果没有设置MachineFlag.Name和DebugFlag.Name
		debugLogger = logger.NewStructLogger(logconfig) //debugLogger是日志结构体
	}

	initialGas := ctx.Uint64(GasFlag.Name)  //initialGas是初始Gas
	genesisConfig := new(core.Genesis)      //genesisConfig是创世区块
	genesisConfig.GasLimit = initialGas     //创世区块的GasLimit等于初始Gas
	if ctx.String(GenesisFlag.Name) != "" { //GenesisFlag.Name = "genesis" 意思是创世区块
		genesisConfig = readGenesis(ctx.String(GenesisFlag.Name)) //读取创世区块
		if genesisConfig.GasLimit != 0 {                          //如果创世区块的GasLimit不等于0
			initialGas = genesisConfig.GasLimit //初始Gas等于创世区块的GasLimit
		}
	} else {
		genesisConfig.Config = params.AllDevChainProtocolChanges //如果没有设置GenesisFlag.Name，那么就使用params.AllDevChainProtocolChanges
	}

	db := rawdb.NewMemoryDatabase()              //db是内存数据库
	triedb := trie.NewDatabase(db, &trie.Config{ //triedb是trie数据库 trie是前缀树
		Preimages: preimages,       //Preimages是预映像
		HashDB:    hashdb.Defaults, //HashDB是哈希数据库
	})
	defer triedb.Close()
	genesis := genesisConfig.MustCommit(db, triedb)  //MustCommit是提交创世区块
	sdb := state.NewDatabaseWithNodeDB(db, triedb)   //sdb是状态数据库
	statedb, _ = state.New(genesis.Root(), sdb, nil) //statedb是状态数据库
	chainConfig = genesisConfig.Config               //chainConfig是链配置

	if ctx.String(SenderFlag.Name) != "" { //SenderFlag.Name = "sender" SenderFlag.Usage = "sender address"
		sender = common.HexToAddress(ctx.String(SenderFlag.Name)) //sender是发送者
	}
	statedb.CreateAccount(sender) //创建发送者账户

	if ctx.String(ReceiverFlag.Name) != "" { //ReceiverFlag.Name = "receiver" ReceiverFlag.Usage = "receiver address"
		receiver = common.HexToAddress(ctx.String(ReceiverFlag.Name)) //receiver是接收者
	}

	var code []byte
	codeFileFlag := ctx.String(CodeFileFlag.Name) //CodeFileFlag.Name = "codefile" CodeFileFlag.Usage = "file containing hex code to run"
	codeFlag := ctx.String(CodeFlag.Name)         //CodeFlag.Name = "code" CodeFlag.Usage = "hex code to run"

	// The '--code' or '--codefile' flag overrides code in state
	if codeFileFlag != "" || codeFlag != "" { //如果设置了CodeFileFlag.Name或者CodeFlag.Name
		var hexcode []byte
		if codeFileFlag != "" { //如果设置了CodeFileFlag.Name
			var err error
			// If - is specified, it means that code comes from stdin
			if codeFileFlag == "-" { //如果CodeFileFlag.Name的值是"-"
				//Try reading from stdin
				if hexcode, err = io.ReadAll(os.Stdin); err != nil { //从标准输入读取
					fmt.Printf("Could not load code from stdin: %v\n", err)
					os.Exit(1)
				}
			} else {
				// Codefile with hex assembly
				if hexcode, err = os.ReadFile(codeFileFlag); err != nil { //从文件读取
					fmt.Printf("Could not load code from file: %v\n", err)
					os.Exit(1)
				}
			}
		} else {
			hexcode = []byte(codeFlag) //如果设置了CodeFlag.Name
		}
		hexcode = bytes.TrimSpace(hexcode) //去除空格
		if len(hexcode)%2 != 0 {           //如果长度不是偶数
			fmt.Printf("Invalid input length for hex data (%d)\n", len(hexcode))
			os.Exit(1)
		}
		code = common.FromHex(string(hexcode)) //将字符串转换为字节切片
	} else if fn := ctx.Args().First(); len(fn) > 0 { //如果没有设置CodeFileFlag.Name和CodeFlag.Name，那么就使用命令行参数
		// EASM-file to compile
		src, err := os.ReadFile(fn) //从文件读取
		if err != nil {
			return err
		}
		bin, err := compiler.Compile(fn, src, false) //编译
		if err != nil {
			return err
		}
		code = common.Hex2Bytes(bin) //将十六进制字符串转换为字节切片
	}
	runtimeConfig := runtime.Config{ //runtimeConfig是运行时配置
		Origin:      sender,                                       //Origin是发送者
		State:       statedb,                                      //State是状态数据库
		GasLimit:    initialGas,                                   //GasLimit是初始Gas
		GasPrice:    flags.GlobalBig(ctx, PriceFlag.Name),         //GasPrice是Gas价格
		Value:       flags.GlobalBig(ctx, ValueFlag.Name),         //Value是价值
		Difficulty:  genesisConfig.Difficulty,                     //Difficulty是难度
		Time:        genesisConfig.Timestamp,                      //Time是时间戳
		Coinbase:    genesisConfig.Coinbase,                       //Coinbase是矿工地址
		BlockNumber: new(big.Int).SetUint64(genesisConfig.Number), //BlockNumber是区块号
		BlobHashes:  blobHashes,                                   //BlobHashes是Blob哈希
		BlobBaseFee: blobBaseFee,                                  //BlobBaseFee是Blob基础费用
		EVMConfig: vm.Config{ //EVMConfig是虚拟机配置
			Tracer: tracer, //Tracer是虚拟机的日志
		},
	}

	if chainConfig != nil { //如果chainConfig不为空
		runtimeConfig.ChainConfig = chainConfig //runtimeConfig.ChainConfig是链配置
	} else {
		runtimeConfig.ChainConfig = params.AllEthashProtocolChanges //如果chainConfig为空，那么就使用params.AllEthashProtocolChanges
	}

	var hexInput []byte
	if inputFileFlag := ctx.String(InputFileFlag.Name); inputFileFlag != "" { //InputFileFlag.Name = "inputfile" InputFileFlag.Usage = "file containing hex input data"
		var err error
		if hexInput, err = os.ReadFile(inputFileFlag); err != nil { //从文件读取
			fmt.Printf("could not load input from file: %v\n", err)
			os.Exit(1)
		}
	} else {
		hexInput = []byte(ctx.String(InputFlag.Name)) //InputFlag.Name = "input" InputFlag.Usage = "hex input data"
	}
	hexInput = bytes.TrimSpace(hexInput) //去除空格
	if len(hexInput)%2 != 0 {            //如果长度不是偶数
		fmt.Println("input length must be even")
		os.Exit(1)
	}
	input := common.FromHex(string(hexInput)) //将十六进制字符串转换为字节切片

	var execFunc func() ([]byte, uint64, error) //execFunc是执行函数
	if ctx.Bool(CreateFlag.Name) {              //CreateFlag.Name = "create" CreateFlag.Usage = "create a contract"
		input = append(code, input...)              //将code和input合并
		execFunc = func() ([]byte, uint64, error) { //execFunc是执行函数
			output, _, gasLeft, err := runtime.Create(input, &runtimeConfig) //Create是创建合约
			return output, gasLeft, err                                      //返回output, gasLeft, err
		}
	} else { //如果没有设置CreateFlag.Name
		if len(code) > 0 { //如果code的长度大于0
			statedb.SetCode(receiver, code) //设置接收者的代码
		}
		execFunc = func() ([]byte, uint64, error) { //execFunc是执行函数
			return runtime.Call(receiver, input, &runtimeConfig) //Call是调用合约
		}
	}

	bench := ctx.Bool(BenchFlag.Name)                             //BenchFlag.Name = "bench" BenchFlag.Usage = "benchmark execution"
	output, leftOverGas, stats, err := timedExec(bench, execFunc) //timedExec是计时执行

	if ctx.Bool(DumpFlag.Name) { //DumpFlag.Name = "dump" DumpFlag.Usage = "dump preimages"
		statedb.Commit(genesisConfig.Number, true) //提交
		fmt.Println(string(statedb.Dump(nil)))     //打印
	}

	if ctx.Bool(DebugFlag.Name) { //DebugFlag.Name = "debug" DebugFlag.Usage = "enable debug logging"
		if debugLogger != nil { //如果debugLogger不为空
			fmt.Fprintln(os.Stderr, "#### TRACE ####")             //Stderr是标准错误输出
			logger.WriteTrace(os.Stderr, debugLogger.StructLogs()) //WriteTrace是写入日志
		}
		fmt.Fprintln(os.Stderr, "#### LOGS ####")   //Stderr是标准错误输出
		logger.WriteLogs(os.Stderr, statedb.Logs()) //WriteLogs是写入日志
	}

	if bench || ctx.Bool(StatDumpFlag.Name) { //StatDumpFlag.Name = "statdump" StatDumpFlag.Usage = "dump stats"
		fmt.Fprintf(os.Stderr, `EVM gas used:    %d
execution time:  %v
allocations:     %d
allocated bytes: %d
`, initialGas-leftOverGas, stats.time, stats.allocs, stats.bytesAllocated) //Stderr是标准错误输出
	}
	if tracer == nil { //如果tracer为空
		fmt.Printf("%#x\n", output) //打印
		if err != nil {
			fmt.Printf(" error: %v\n", err)
		}
	}

	return nil
}
