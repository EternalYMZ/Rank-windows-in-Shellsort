# 一段排序还留下多少工作？看相邻秩落在哪些槽

取最终秩连续的一小段，例如秩 $10$ 到 $17$。排好以后这八个键中应有四个在偶数槽。如果某个中间状态有六个在偶数槽，往后只使用偶数间隔就一直是六个。必须有能跨奇偶的动作才能修复这份偏差。问题在于，能否仅凭已经执行的前几趟，就证明这样的偏差很常见？

**按秩开窗。** 固定窗长 $L$ 和模数 $d$，逐窗比较每个槽号余类的当前计数与最终计数。一次成功交换至多让两个键改变余类；若 $d$ 整除该趟间隔，连这两个键的余类也不变。一个键又至多属于 $L$ 个这样的窗。把每个动作能改动的账目数清，就能把观察到的偏差转为余下工作量的下界。相邻窗口往往重叠，不能把各窗所需交换直接相加。[余类变化与实际右移](https://github.com/EternalYMZ/Rank-windows-in-Shellsort/blob/a8795aae4f3a2619844bcfcd6b74896544a7a048/Shellsort/PaidResidueWindows.lean) · [六槽算例](https://github.com/EternalYMZ/Rank-windows-in-Shellsort/blob/a8795aae4f3a2619844bcfcd6b74896544a7a048/SixSlotExample.lean)

**按信息的传播范围估计下一趟。** 从输出槽逆着预定前缀 $w$ 往回走，每遇一趟就将当时所在的整条间隔链都列为可能来源；一路回到原数组，得到一个只由 $w$ 决定的集合。假设每个输出槽的来源集合至多有 $B$ 个成员，每个原始槽也至多出现在 $B$ 个这样的集合中。对下一间隔 $g\ge1$，若 $B\ge1$ 且 $8gB^3\le n$，公开 Lean 定理给出均匀随机排列上的下界
$$
\mathbb E C_{\mathrm{next}}\ \ge\ \mathbb E I_g\ \ge\ \frac{n^2}{128gB}.
$$
证明先从某些来源互不相交的槽对上估计逆序概率，再把这些槽对在各条 $g$ 链上加起来；最后用线性插入每次成功右移都要比较，将逆序下界转为真实比较下界。[下一趟的均匀输入定理](https://github.com/EternalYMZ/Rank-windows-in-Shellsort/blob/a8795aae4f3a2619844bcfcd6b74896544a7a048/Shellsort/PrefixRankSymmetrization.lean)

若只知道前缀的趟数和移动预算，未必已有上面两个 $B$ 界。由短前缀的比较记录推导许多秩窗同时保留偏差，是项目的另一层解析论证。
