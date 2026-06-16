# Logos

Logos 是一个用于辅助 LLM 验证 SQL schema rewrites 等价性的自动化定理证明器。项目目标是使用 Rocq 构建可检查的证明对象，让 LLM 负责提出 rewrite、lemma 和归纳结构，而最终等价性结论由证明器验证。

## SQL 形式化语义

Logos 的 SQL 形式化语义部分基于已有的 SQLCoq 工作：

- `vendor/FormalSQL`: SQLCoq/SQLFormalSemantics 的 Rocq 迁移 fork，包含 SQL 抽象语法、bag semantics、SQLAlgebra，以及 `eval_sql_query` / `eval_query` 等语义定义。

我们计划优先把 Logos 的等价性证明层建立在 SQLCoq 的语义定义之上，而不是重新定义 SQL 语义。典型证明目标会接近：

```coq
forall instance env,
  well_sorted_sql_table T basesort instance ->
  eval_sql_query env q_before =BE= eval_sql_query env q_after.
```

对于更适合代数化推理的 rewrite，可以使用 SQLCoq 自带的 `SQLAlgebra` 层证明等价。Logos 不再 vendor SQLToNRACert/DBCert，也不把 SQL 翻译到 Q*Cert NRAEnv 或 JavaScript 编译链；这些路径是为 certified SQL-to-JS 服务的，不是当前 rewrite 等价性验证的核心依赖。

## 子模块

本仓库通过 Git submodule 固定 SQLCoq 相关依赖：

```bash
git submodule update --init --recursive
```

当前配置如下：

```text
vendor/FormalSQL  git@github.com:WindOctober/FormalSQL.git  branch master
```

## 构建说明

Logos 使用 `vendor/FormalSQL` 中已经迁移到 Rocq 的 SQLCoq fork。默认使用同一工作区中 `../FormalSQL/.opam-rocq` 这个 Rocq 9.2 switch；需要其它 switch 时可以覆盖 `OPAM_SWITCH`。

```bash
make submodules
make formal-sql
make smoke
```

这个 smoke test 会编译 `theories/Smoke.v`，确认 Logos 本地 Rocq 文件能够导入 SQLCoq 的 `SQLFS` 语义库。

如果已经手动创建了兼容环境，也可以只运行：

```bash
make submodules
make status
```

## SQLCoq 维护状态

上游 SQLCoq 仓库不是面向现代 Rocq 的活跃维护栈：

- upstream `sqlformalsemantics` 当前仍以 Coq 8.11.2 为基线。
- `vendor/FormalSQL` 是 `WindOctober/FormalSQL` 的 `master` 分支，fork 自 `formaldata/sqlformalsemantics`，目标是在保持 SQL 形式化语义不变的基础上支持 Rocq 9.2。

因此，Logos 当前只依赖 FormalSQL 的 SQL 语义和 SQLAlgebra，不依赖 SQLToNRACert、DBCert 或 Q*Cert 的 NRA/JavaScript 编译链。
