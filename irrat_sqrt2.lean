/-
# 根号二无理性证明 by Pot
首次打开需要等待一段时间，直到上方Lean is busy消失，状态条变为绿色
-/

/-导入一些必要的内容-/
import data.rat         -- 有理数
       data.nat.parity  -- 自然数的奇偶性
       tactic           -- 证明策略（一个tactic相当于证明中的一小步）


-- 先来看一个关于命题逻辑的简单引理

/-引理   名称       (已知条件)   : 要证明的命题 -/
lemma self_or_self {P : Prop} :   P ∨ P ↔ P   :=
begin
  -- begin 与 end 之间是引理的证明

  -- 屏幕右侧的'infoview'窗口记录了当前状态下的 已知条件 和 证明目标(⊢)

  -- 将鼠标点击到行末可以看到本行的tactic如何改变了当前状态

  split,  -- 将一个目标分为两个；分别证明 ↔ 的两个方向 
  {
    -- 一对花括号专注于解决一个目标

    -- 假设 P ∨ P, 命名为 h
    intro h,

    -- h 是一个或命题，将 h 拆分为 h1 h2 (分别在 h1 或 h2成立的条件下证明目标)
    cases h with h1 h2,
    {
      exact h1,  -- 要证明的目标就是已知的 h1
    },
    {exact h2},
  },
  {
    -- 假设 P,命名为 p
    intro p,
    -- 要证明或命题，只需要证明 ∨ 左边的命题（当然右边也可以）
    left,
    exact p,
  }
end

/- 平方是偶数的自然数一定是偶数 -/
lemma even_if_square_even {n : ℕ} (hn2 : even (n*n)) : even n :=
begin
  rw nat.even_mul at hn2,   --  nat.even_mul : m * n 是偶数 ↔ m 是偶数或 n 是偶数
  rw self_or_self at hn2,   -- 引用上一条引理，改写了hn2
  exact hn2,
end

/- 偶数一定可以被2整除 -/
lemma div2_if_even {n : ℕ} (h_even: even n) : (2 ∣ n) :=
begin
  rw even at *,   -- 将 even 谓词改写成其定义形式
  cases h_even with r hr, -- 存在命题可以拆分为 存在的元素 及其 性质

  -- 根据整除的定义，要证明 2 ∣ n, 需要找到一个整数 k 使得 n = 2k
  use r,  -- 显然 r 是满足条件的
  rw [mul_comm,   -- r * 2 改写为 2 * r
      mul_two],   -- 2 * r 改写为 r + r
  exact hr,
end

/- 不存在平方等于 2 的有理数 -/
theorem sqrt_2_irrational : ¬ ∃ q : ℚ , q * q = 2 :=
begin
  by_contra,  -- 使用反证法
  cases h with q hq,

  -- m := q 分子的绝对值，n :=  q 分母
  set m := int.nat_abs q.num with hm,
  set n := q.denom with hn,
  -- 注意 m n都是自然数

  -- 根据有理数的定义 q 是既约分数，所以 m n 互质
  have m_n_coprime : nat.coprime m n := q.cop,

  -- 注意到将 hq 整理可得如下等式，证明如下（有难度，可跳过）
  have eq : m * m = 2 * (n * n) := begin
    -- 注意到 |分子|^2 = 分子^2
    have hm2 : q.num * q.num = m * m := begin
      norm_cast,  -- 注意到等式左边为整数，右侧为自然数，将右侧类型转化的函数整理出来（不理解可以跳过）
      rw [hm, int.nat_abs_mul_self],-- 平方可以消去绝对值
    end,

    rw [rat.eq_iff_mul_eq_mul,  
        rat.mul_self_num, 
        rat.mul_self_denom,
        hm2,
        ←hn] at hq, -- 将 q 的分母乘到等式右侧

    norm_cast at hq,--化简
    rw mul_one at hq,--消去等式左边的1
    exact hq,
  end,

  /- 注意到 m 一定是偶数，证明如下-/
  have even_m : even m := begin
    /- 先证明 m * m是偶数 -/
    have even_mm : even (m * m) := begin
      rw even,      -- 根据定义，只要找到一个自然数 r 使得 m * m = r + r
      use (n * n),  -- n + n满足条件
      rw [←mul_two, mul_comm (n*n) 2],--整理
      exact eq,
    end,

    /-根据前面的引理，m是偶数-/
    exact even_if_square_even even_mm,
  end,

  /- 注意到 n 也一定是偶数，证明如下 -/
  have even_n : even n := begin
    /- 同样先证明 n*n 是偶数-/
    have even_nn : even (n * n) := begin

      cases even_m with k hk,-- m是偶数，所以存在k : ℕ，使得 m = k + k
      rw hk at eq, -- 把 eq 中的 m 改写为 k + k

      /- 注意到eq的左边可以化为如下形式，
      因为k是自然数，且 + * 对 ℕ 构成 交换半环，所以可以使用 ring 自动证明-/
      have eq_left: (k + k) * (k + k) = 2 * (k^2 + k^2) :=by ring, 
      rw eq_left at eq,
      
      -- 显然 k^2 满足 n * n = k^2 + k^2
      use (k^2),
      -- 在eq的左右两端同时除以2即可得到，较简单，使用linarith自动证明
      linarith [eq],
    end,

    exact even_if_square_even even_nn,-- 根据上面的引理，n 也是偶数
  end,

  /- 注意到 m n 都是偶数，所以 m n 并不互质-/
  have m_n_not_coprime : ¬ nat.coprime m n :=begin
    apply @nat.not_coprime_of_dvd_of_dvd m n 2,-- m n 可以被 2 整除，2 > 1, 所以 m n不互质
      norm_num,-- 证明 2 > 1
      {
        -- 证明 m 可以被 2 整除
        apply div2_if_even, -- 根据引理：偶数一定可以被 2 整除
        exact even_m,
      },
      {
        -- 证明 n 可以被 2 整除
        apply div2_if_even,
        exact even_n,
      }
  end,
  
  -- 至此，我们已经同时证明了 m.coprime n 和 ¬ m.coprime n，二者构成矛盾，使得false可以被证明
  
  -- 在Lean中，¬ P 定义为 P → false
  apply m_n_not_coprime,  -- 要证明false，只要证明 m.coprime n
  exact m_n_coprime,      -- m.coprime n 已经证明过了
end

