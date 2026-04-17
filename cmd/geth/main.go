// Copyright 2014 The go-ethereum Authors
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

// geth is a command-line client for Ethereum.
//
// 本文件职责概览：
//   - 注册全局命令行参数（节点 / RPC / 指标等），定义默认动作为启动完整节点；
//   - 无子命令时执行 geth()：makeFullNode（见 config.go）创建 node.Node，再 startNode 启动并阻塞在 stack.Wait()。
package main

import (
	"fmt"
	"os"
	"slices"
	"sort"
	"time"

	"github.com/ethereum/go-ethereum/accounts"
	"github.com/ethereum/go-ethereum/cmd/utils"
	"github.com/ethereum/go-ethereum/common"
	"github.com/ethereum/go-ethereum/console/prompt"
	"github.com/ethereum/go-ethereum/eth/downloader"
	"github.com/ethereum/go-ethereum/ethclient"
	"github.com/ethereum/go-ethereum/internal/debug"
	"github.com/ethereum/go-ethereum/internal/flags"
	"github.com/ethereum/go-ethereum/log"
	"github.com/ethereum/go-ethereum/node"
	"go.uber.org/automaxprocs/maxprocs"

	// Force-load the tracer engines to trigger registration
	// 空导入：仅触发各 tracer 包的 init 注册，否则可能因无直接引用被编译器裁掉。
	_ "github.com/ethereum/go-ethereum/eth/tracers/js"
	_ "github.com/ethereum/go-ethereum/eth/tracers/live"
	_ "github.com/ethereum/go-ethereum/eth/tracers/native"

	"github.com/urfave/cli/v2"
)

const (
	clientIdentifier = "geth" // 在网络中对外标识本客户端名称
)

// 全局 flag 分组：nodeFlags（节点）、rpcFlags（RPC）、consoleFlags（控制台）、debug.Flags（调试）、metricsFlags（指标）。
var (
	// nodeFlags：与链、同步、交易池、缓存、P2P、信标链、开发模式等相关的节点级参数（定义在 cmd/utils）。
	nodeFlags = slices.Concat([]cli.Flag{
		utils.IdentityFlag,
		utils.UnlockedAccountFlag,
		utils.PasswordFileFlag,
		utils.BootnodesFlag,
		utils.MinFreeDiskSpaceFlag,
		utils.KeyStoreDirFlag,
		utils.ExternalSignerFlag,
		utils.NoUSBFlag, // deprecated
		utils.USBFlag,
		utils.SmartCardDaemonPathFlag,
		utils.OverrideOsaka,
		utils.OverrideBPO1,
		utils.OverrideBPO2,
		utils.OverrideVerkle,
		utils.OverrideGenesisFlag,
		utils.EnablePersonal, // deprecated
		utils.TxPoolLocalsFlag,
		utils.TxPoolNoLocalsFlag,
		utils.TxPoolJournalFlag,
		utils.TxPoolRejournalFlag,
		utils.TxPoolPriceLimitFlag,
		utils.TxPoolPriceBumpFlag,
		utils.TxPoolAccountSlotsFlag,
		utils.TxPoolGlobalSlotsFlag,
		utils.TxPoolAccountQueueFlag,
		utils.TxPoolGlobalQueueFlag,
		utils.TxPoolLifetimeFlag,
		utils.BlobPoolDataDirFlag,
		utils.BlobPoolDataCapFlag,
		utils.BlobPoolPriceBumpFlag,
		utils.SyncModeFlag,
		utils.SyncTargetFlag,
		utils.ExitWhenSyncedFlag,
		utils.GCModeFlag,
		utils.SnapshotFlag,
		utils.TxLookupLimitFlag, // deprecated
		utils.TransactionHistoryFlag,
		utils.ChainHistoryFlag,
		utils.LogHistoryFlag,
		utils.LogNoHistoryFlag,
		utils.LogExportCheckpointsFlag,
		utils.StateHistoryFlag,
		utils.TrienodeHistoryFlag,
		utils.TrienodeHistoryFullValueCheckpointFlag,
		utils.LightKDFFlag,
		utils.EthRequiredBlocksFlag,
		utils.LegacyWhitelistFlag, // deprecated
		utils.CacheFlag,
		utils.CacheDatabaseFlag,
		utils.CacheTrieFlag,
		utils.CacheTrieJournalFlag,   // deprecated
		utils.CacheTrieRejournalFlag, // deprecated
		utils.CacheGCFlag,
		utils.CacheSnapshotFlag,
		utils.CacheNoPrefetchFlag,
		utils.CachePreimagesFlag,
		utils.CacheLogSizeFlag,
		utils.FDLimitFlag,
		utils.CryptoKZGFlag,
		utils.ListenPortFlag,
		utils.DiscoveryPortFlag,
		utils.MaxPeersFlag,
		utils.MaxPendingPeersFlag,
		utils.MiningEnabledFlag, // deprecated
		utils.MinerGasLimitFlag,
		utils.MinerGasPriceFlag,
		utils.MinerEtherbaseFlag, // deprecated
		utils.MinerExtraDataFlag,
		utils.MinerMaxBlobsFlag,
		utils.MinerRecommitIntervalFlag,
		utils.MinerPendingFeeRecipientFlag,
		utils.MinerNewPayloadTimeoutFlag, // deprecated
		utils.NATFlag,
		utils.NoDiscoverFlag,
		utils.DiscoveryV4Flag,
		utils.DiscoveryV5Flag,
		utils.LegacyDiscoveryV5Flag, // deprecated
		utils.NetrestrictFlag,
		utils.NodeKeyFileFlag,
		utils.NodeKeyHexFlag,
		utils.DNSDiscoveryFlag,
		utils.DeveloperFlag,
		utils.DeveloperGasLimitFlag,
		utils.DeveloperPeriodFlag,
		utils.VMEnableDebugFlag,
		utils.VMTraceFlag,
		utils.VMTraceJsonConfigFlag,
		utils.VMWitnessStatsFlag,
		utils.VMStatelessSelfValidationFlag,
		utils.NetworkIdFlag,
		utils.EthStatsURLFlag,
		utils.GpoBlocksFlag,
		utils.GpoPercentileFlag,
		utils.GpoMaxGasPriceFlag,
		utils.GpoIgnoreGasPriceFlag,
		configFileFlag,
		utils.LogDebugFlag,
		utils.LogBacktraceAtFlag,
		utils.BeaconApiFlag,
		utils.BeaconApiHeaderFlag,
		utils.BeaconThresholdFlag,
		utils.BeaconNoFilterFlag,
		utils.BeaconConfigFlag,
		utils.BeaconGenesisRootFlag,
		utils.BeaconGenesisTimeFlag,
		utils.BeaconCheckpointFlag,
		utils.BeaconCheckpointFileFlag,
		utils.LogSlowBlockFlag,
	}, utils.NetworkFlags, utils.DatabaseFlags)

	// rpcFlags：HTTP/WS/IPC/Auth/GraphQL 及 RPC 限额、遥测等对外接口相关参数。
	rpcFlags = []cli.Flag{
		utils.HTTPEnabledFlag,
		utils.HTTPListenAddrFlag,
		utils.HTTPPortFlag,
		utils.HTTPCORSDomainFlag,
		utils.AuthListenFlag,
		utils.AuthPortFlag,
		utils.AuthVirtualHostsFlag,
		utils.JWTSecretFlag,
		utils.HTTPVirtualHostsFlag,
		utils.GraphQLEnabledFlag,
		utils.GraphQLCORSDomainFlag,
		utils.GraphQLVirtualHostsFlag,
		utils.HTTPApiFlag,
		utils.HTTPPathPrefixFlag,
		utils.WSEnabledFlag,
		utils.WSListenAddrFlag,
		utils.WSPortFlag,
		utils.WSApiFlag,
		utils.WSAllowedOriginsFlag,
		utils.WSPathPrefixFlag,
		utils.IPCDisabledFlag,
		utils.IPCPathFlag,
		utils.InsecureUnlockAllowedFlag,
		utils.RPCGlobalGasCapFlag,
		utils.RPCGlobalEVMTimeoutFlag,
		utils.RPCGlobalTxFeeCapFlag,
		utils.RPCGlobalLogQueryLimit,
		utils.AllowUnprotectedTxs,
		utils.BatchRequestLimit,
		utils.BatchResponseMaxSize,
		utils.RPCTxSyncDefaultTimeoutFlag,
		utils.RPCTxSyncMaxTimeoutFlag,
		utils.RPCGlobalRangeLimitFlag,
		utils.RPCTelemetryFlag,
		utils.RPCTelemetryEndpointFlag,
		utils.RPCTelemetryUserFlag,
		utils.RPCTelemetryPasswordFlag,
		utils.RPCTelemetryInstanceIDFlag,
		utils.RPCTelemetryTagsFlag,
		utils.RPCTelemetrySampleRatioFlag,
	}

	// metricsFlags：Prometheus/InfluxDB 等指标导出相关参数。
	metricsFlags = []cli.Flag{
		utils.MetricsEnabledFlag,
		utils.MetricsEnabledExpensiveFlag,
		utils.MetricsHTTPFlag,
		utils.MetricsPortFlag,
		utils.MetricsEnableInfluxDBFlag,
		utils.MetricsInfluxDBEndpointFlag,
		utils.MetricsInfluxDBDatabaseFlag,
		utils.MetricsInfluxDBUsernameFlag,
		utils.MetricsInfluxDBPasswordFlag,
		utils.MetricsInfluxDBTagsFlag,
		utils.MetricsInfluxDBIntervalFlag,
		utils.MetricsEnableInfluxDBV2Flag,
		utils.MetricsInfluxDBTokenFlag,
		utils.MetricsInfluxDBBucketFlag,
		utils.MetricsInfluxDBOrganizationFlag,
		utils.StateSizeTrackingFlag,
	}
)

// app：整个 geth 进程的 CLI 根对象（子命令与全局 flag 均挂在此上）。
// 初始化 app 对象，设置默认行为为启动节点。
var app = flags.NewApp("the go-ethereum command line interface")

func init() { //
	// 未写子命令时（例如直接执行 geth）的默认行为：启动节点。
	app.Action = geth              //没有写子命令 那么直接给acction行动配置默认 geth 即启动节点
	app.Commands = []*cli.Command{ // 子命令
		// See chaincmd.go:
		initCommand,
		importCommand,
		exportCommand,
		importHistoryCommand,
		exportHistoryCommand,
		importPreimagesCommand,
		removedbCommand,
		dumpCommand,
		dumpGenesisCommand,
		pruneHistoryCommand,
		downloadEraCommand,
		// See accountcmd.go:
		accountCommand,
		walletCommand,
		// See consolecmd.go:
		consoleCommand,
		attachCommand,
		javascriptCommand,
		// See misccmd.go:
		versionCommand,
		licenseCommand,
		// See config.go
		dumpConfigCommand,
		// see dbcmd.go
		dbCommand,
		// See cmd/utils/flags_legacy.go
		utils.ShowDeprecated,
		// See snapshot.go
		snapshotCommand,
	}
	if logTestCommand != nil { // 如果 logTestCommand 不为 nil logtestcmd_active.go意思是日志测试命令 如果构建了集成测试 那么就添加logtest命令
		app.Commands = append(app.Commands, logTestCommand) //给子命令添加logtest命令
	}
	sort.Sort(cli.CommandsByName(app.Commands)) //用排序指令对子命令进行排序

	// 合并所有全局 flag；consoleFlags 在 consolecmd.go 中定义。
	app.Flags = slices.Concat( // 合并所有全局 flag；consoleFlags 在 consolecmd.go 中定义。
		nodeFlags,    // 节点 flag
		rpcFlags,     // RPC flag
		consoleFlags, // 控制台 flag
		debug.Flags,  // 调试 flag
		metricsFlags, // 指标 flag
	)
	// 支持用环境变量覆盖，例如 GETH_HTTP_PORT 对应 --http.port。
	flags.AutoEnvVars(app.Flags, "GETH")

	// 每次命令执行前：容器内 CPU 配额、全局 flag 迁移、日志与 pprof 等调试设施。
	app.Before = func(ctx *cli.Context) error {
		maxprocs.Set() // Automatically set GOMAXPROCS to match Linux container CPU quota.
		flags.MigrateGlobalFlags(ctx)
		if err := debug.Setup(ctx); err != nil {
			return err
		}
		flags.CheckEnvVars(ctx, app.Flags, "GETH")
		return nil
	}
	// 命令结束后：关闭调试、恢复终端（控制台模式会改 tty）。
	app.After = func(ctx *cli.Context) error {
		debug.Exit()
		prompt.Stdin.Close() // Resets terminal mode.
		return nil
	}
}

func main() {
	// 解析 os.Args 并分发到默认 Action 或某一子命令。
	if err := app.Run(os.Args); err != nil {
		fmt.Fprintln(os.Stderr, err)
		os.Exit(1)
	}
}

// prepare manipulates memory cache allowance and setups metric system.
// This function should be called before launching devp2p stack.
//
// 在真正起节点前打一条日志，便于从输出判断当前是主网还是某个测试网预设。
func prepare(ctx *cli.Context) {
	switch {
	case ctx.IsSet(utils.SepoliaFlag.Name):
		log.Info("Starting Geth on Sepolia testnet...")

	case ctx.IsSet(utils.HoleskyFlag.Name):
		log.Info("Starting Geth on Holesky testnet...")

	case ctx.IsSet(utils.HoodiFlag.Name):
		log.Info("Starting Geth on Hoodi testnet...")

	case !ctx.IsSet(utils.NetworkIdFlag.Name):
		log.Info("Starting Geth on Ethereum mainnet...")
	}
}

// geth is the main entry point into the system if no special subcommand is run.
// It creates a default node based on the command line arguments and runs it in
// blocking mode, waiting for it to be shut down.
//
// 默认入口：构造节点（makeFullNode 在 config.go）、启动服务，然后阻塞直到进程退出。
func geth(ctx *cli.Context) error {
	// 默认 Action 不接受额外位置参数；多余参数视为误输入。
	if args := ctx.Args().Slice(); len(args) > 0 { // 如果 args 不为空 那么返回错误
		return fmt.Errorf("invalid command: %q", args[0]) // 返回错误 无效命令
	}

	prepare(ctx)               // 准备 设置内存缓存允许和设置指标系统 在真正起节点前打一条日志，便于从输出判断当前是主网还是某个测试网预设。
	stack := makeFullNode(ctx) // 构造节点（makeFullNode 在 config.go）
	defer stack.Close()        // defer 延迟关闭节点

	startNode(ctx, stack, false) // 启动节点 启动已注册的 Ethereum 等协议、RPC/IPC；后台处理硬件钱包热插拔与可选的「同步完退出」。
	stack.Wait()                 // 阻塞主 goroutine，直到 stack.Close() 或信号关闭
	return nil
}

// startNode boots up the system node and all registered protocols, after which
// it starts the RPC/IPC interfaces and the miner.
//
// 启动已注册的 Ethereum 等协议、RPC/IPC；后台处理硬件钱包热插拔与可选的「同步完退出」。
func startNode(ctx *cli.Context, stack *node.Node, isConsole bool) {
	utils.StartNode(ctx, stack, isConsole) // 启动节点 启动已注册的 Ethereum 等协议、RPC/IPC；后台处理硬件钱包热插拔与可选的「同步完退出」。

	if ctx.IsSet(utils.UnlockedAccountFlag.Name) { // 如果 unlockedaccountflag 被设置 那么警告 这个标志已经弃用 并且没有效果
		log.Warn(`The "unlock" flag has been deprecated and has no effect`) // 警告 这个标志已经弃用 并且没有效果
	}

	// 订阅钱包事件：USB/Ledger 等插入时打开并做 HD 派生地址（需连上本机 ethclient）。
	events := make(chan accounts.WalletEvent, 16) // 创建一个通道 用于订阅钱包事件 walletevent 是钱包事件的类型
	stack.AccountManager().Subscribe(events)      // 订阅钱包事件：USB/Ledger 等插入时打开并做 HD 派生地址（需连上本机 ethclient）。

	rpcClient := stack.Attach()                 // 附加 附加到节点 返回一个 rpc 客户端
	ethClient := ethclient.NewClient(rpcClient) // 创建一个以太坊客户端 返回一个以太坊客户端  用ethclient连接到rpcclient 包一层客户端 方便使用ethclient的函数

	// 后台 goroutine：不阻塞主流程；负责「已连接钱包先打开」+「之后热插拔事件」。
	go func() {
		// 节点启动这一刻已经注册在 AccountManager 里的钱包（例如已插着的硬件钱包）。
		for _, wallet := range stack.AccountManager().Wallets() {
			if err := wallet.Open(""); err != nil {
				// 英文日志：打开失败。中文含义：启动时尝试打开已有钱包失败（url=钱包标识，err=原因）。
				log.Warn("Failed to open wallet", "url", wallet.URL(), "err", err)
			}
		}
		// 阻塞在此，直到 channel 关闭；持续处理新插入/打开/拔掉等事件。
		for event := range events {
			switch event.Kind {
			case accounts.WalletArrived:
				if err := event.Wallet.Open(""); err != nil {
					// 英文日志：新设备出现但打开失败。中文含义：检测到新钱包但未能打开。
					log.Warn("New wallet appeared, failed to open", "url", event.Wallet.URL(), "err", err)
				}
			case accounts.WalletOpened:
				status, _ := event.Wallet.Status()
				// 英文日志：新钱包已出现。中文含义：钱包已成功打开；status 为设备返回的状态字符串。
				log.Info("New wallet appeared", "url", event.Wallet.URL(), "status", status)

				var derivationPaths []accounts.DerivationPath
				if event.Wallet.URL().Scheme == "ledger" {
					// Ledger 需多试一条旧版派生路径，再试标准路径。
					derivationPaths = append(derivationPaths, accounts.LegacyLedgerBaseDerivationPath)
				}
				derivationPaths = append(derivationPaths, accounts.DefaultBaseDerivationPath)

				// 按上述 BIP44 路径向链上查询并缓存派生出的账户（用本机 ethClient）。
				event.Wallet.SelfDerive(derivationPaths, ethClient)

			case accounts.WalletDropped:
				// 英文日志：旧钱包已移除。中文含义：设备拔掉或钱包从管理器移除。
				log.Info("Old wallet dropped", "url", event.Wallet.URL())
				event.Wallet.Close()
			}
		}
	}()

	//因为有些常见不需要节点一直开着，同步到足够新的时候自动关闭节点，比如批处理/CI 等场景
	// --exitwhensynced：同步完成且链尖足够新时自动关闭节点（用于批处理/CI 等场景）。
	if ctx.Bool(utils.ExitWhenSyncedFlag.Name) {
		go func() { // 后台 goroutine：不阻塞主流程；负责「同步完成且链尖足够新时自动关闭节点」。
			sub := stack.EventMux().Subscribe(downloader.DoneEvent{}) // 订阅下载完成事件
			defer sub.Unsubscribe()                                   // 取消订阅下载完成事件
			for {
				event := <-sub.Chan() // 获取下载完成事件
				if event == nil {
					continue // 如果事件为空 那么继续获取下一个事件
				}
				done, ok := event.Data.(downloader.DoneEvent)
				if !ok {
					continue
				}
				if timestamp := time.Unix(int64(done.Latest.Time), 0); time.Since(timestamp) < 10*time.Minute {
					log.Info("Synchronisation completed", "latestnum", done.Latest.Number, "latesthash", done.Latest.Hash(),
						"age", common.PrettyAge(timestamp))
					stack.Close()
				}
			}
		}()
	}
}
