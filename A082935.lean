import Mathlib

/-!
# OEIS A082935 — kernel-pure formalization

`a082935 n` : smallest palindrome beginning (in decimal) with `n` whose
digit-sum iteration reaches `n` at some stage `k ≥ 1`.
`a082217 n` : same but requiring the first-round digit sum to equal `n`
(0 by convention when the set is empty — only for `n = 19`).

Main results:
* `a082935_eq_self_of_lt10` : `a082935 n = n` for `n ≤ 9`.
* `a082935_eq_w` : for `10 ≤ n`, `n ≠ 19`,
  `a082935 n = ofDigits 10 (digits 10 n).reverse ++ gmid (lmin t) t ++ digits 10 n`
  with `t = n − 2·σ₁₀ n`, `lmin t` = minimal length of a palindromic
  digit-string of sum `t` and `gmid` = the `Nat.ofDigits`-smallest such string.
* `a082935_19` : `a082935 19 = 1949999999999999999999491` (kernel-certified).
* `A082935_formula`, `A082935_wilson_conjecture`, `A082217_characterization`.
-/

noncomputable section

open Classical

/-! ## Definitions -/

/-- Base-10 digit sum. -/
def sigma10 (m : ℕ) : ℕ := (Nat.digits 10 m).sum

/-- `m` begins with `n` in decimal: the little-endian digits of `n` are a
suffix of those of `m`. -/
def beginsWith10 (n m : ℕ) : Prop :=
  Nat.digits 10 n <:+ Nat.digits 10 m

/-- `m` is a decimal palindrome. -/
def isPalindrome10 (m : ℕ) : Prop :=
  List.Palindrome (Nat.digits 10 m)

/-- The digit-sum iteration of `m` reaches `n` at some stage `k ≥ 1`. -/
def reachesDigitSum (n m : ℕ) : Prop :=
  ∃ k : ℕ, 1 ≤ k ∧ sigma10^[k] m = n

/-- OEIS A082935 (sInf ∅ = 0 convention). -/
noncomputable def a082935 (n : ℕ) : ℕ :=
  sInf {m : ℕ | isPalindrome10 m ∧ beginsWith10 n m ∧ reachesDigitSum n m}

/-- OEIS A082217 (sInf ∅ = 0 convention). -/
noncomputable def a082217 (n : ℕ) : ℕ :=
  sInf {m : ℕ | isPalindrome10 m ∧ beginsWith10 n m ∧ sigma10 m = n}

/-- `M` is a palindromic digit-string of length `l`, all digits `< 10`,
with digit sum `t`. -/
def isPalDigitString (l t : ℕ) (M : List ℕ) : Prop :=
  M.length = l ∧ (∀ d ∈ M, d < 10) ∧ M.Palindrome ∧ M.sum = t

/-- Minimal length of a palindromic digit-string with digit sum `t`. -/
noncomputable def lmin (t : ℕ) : ℕ :=
  sInf {l : ℕ | ∃ M : List ℕ, isPalDigitString l t M}

/-- The `Nat.ofDigits`-smallest palindromic digit-string of length `L` and
digit sum `s` (junk value `[]` when no such string exists). -/
noncomputable def gmid (L s : ℕ) : List ℕ :=
  if h : ∃ M : List ℕ, isPalDigitString L s M then
    Classical.choose (Nat.sInf_mem (s := {v : ℕ | ∃ M : List ℕ,
        isPalDigitString L s M ∧ Nat.ofDigits 10 M = v})
      (by obtain ⟨M, hM⟩ := h; exact ⟨Nat.ofDigits 10 M, M, hM, rfl⟩))
  else []

/-! ## Elementary digit lemmas -/

theorem list_sum_le_nine {l : List ℕ} (h : ∀ d ∈ l, d < 10) :
    l.sum ≤ 9 * l.length := by
  induction l with
  | nil => simp
  | cons x xs ih =>
    rw [List.sum_cons, List.length_cons]
    have hx : x < 10 := h x List.mem_cons_self
    have hxs := ih (fun d hd => h d (List.mem_cons_of_mem _ hd))
    omega

theorem sum_le_nine_mul_len (m : ℕ) :
    sigma10 m ≤ 9 * (Nat.digits 10 m).length :=
  list_sum_le_nine (fun d hd =>
    Nat.digits_lt_base (by norm_num : (1 : ℕ) < 10) hd)

theorem pow10_pred_len_le {n : ℕ} (hn : n ≠ 0) :
    10 ^ ((Nat.digits 10 n).length - 1) ≤ n := by
  have hne : Nat.digits 10 n ≠ [] := Nat.digits_ne_nil_iff_ne_zero.mpr hn
  have hpos : 0 < (Nat.digits 10 n).length := List.length_pos_iff.mpr hne
  have h : (Nat.digits 10 n).length - 1 < (Nat.digits 10 n).length := by omega
  exact (Nat.lt_digits_length_iff (by norm_num : (1 : ℕ) < 10) n).mp h

theorem sigma10_le (m : ℕ) : sigma10 m ≤ m :=
  (Nat.sum_le_ofDigits _ (by norm_num : 1 ≤ 10)).trans_eq
    (Nat.ofDigits_digits 10 m)

theorem sigma10_eq_self {m : ℕ} (h : m < 10) : sigma10 m = m := by
  rcases Nat.eq_zero_or_pos m with rfl | hp
  · rfl
  · rw [show sigma10 m = (Nat.digits 10 m).sum from rfl,
        Nat.digits_of_lt 10 m (by omega) h]
    simp

theorem sigma10_lt_self {m : ℕ} (h : 10 ≤ m) : sigma10 m < m := by
  have hdig : Nat.digits 10 m = (m % 10) :: Nat.digits 10 (m / 10) :=
    Nat.digits_def' (by norm_num) (by omega)
  have hm : m % 10 < 10 := Nat.mod_lt _ (by norm_num)
  have hq : 0 < m / 10 := Nat.div_pos (by omega) (by norm_num)
  have h2 : (Nat.digits 10 (m / 10)).sum ≤ m / 10 := sigma10_le _
  rw [show sigma10 m = (Nat.digits 10 m).sum from rfl, hdig, List.sum_cons]
  omega

/-- Once the orbit falls strictly below `n` it stays below `n`. -/
theorem orbit_below {n m : ℕ} (h : sigma10 m < n) :
    ∀ k : ℕ, sigma10^[k + 1] m < n := by
  intro k
  induction k with
  | zero => simpa using h
  | succ k ih =>
    rw [Function.iterate_succ_apply']
    rcases lt_or_ge (sigma10^[k + 1] m) 10 with h10 | h10
    · rw [sigma10_eq_self h10]
      exact ih
    · exact (sigma10_lt_self h10).trans ih

theorem reach_ge {n m : ℕ} (h : reachesDigitSum n m) : n ≤ sigma10 m := by
  obtain ⟨k, hk1, hkm⟩ := h
  cases k with
  | zero => omega
  | succ j =>
    by_contra hlt
    simp only [not_le] at hlt
    exact absurd hkm (ne_of_lt (orbit_below hlt j))

theorem reach2_ge {n m : ℕ} (h : reachesDigitSum n m) (hne : sigma10 m ≠ n) :
    n ≤ sigma10^[2] m := by
  obtain ⟨k, hk1, hkm⟩ := h
  cases k with
  | zero => omega
  | succ k =>
    cases k with
    | zero =>
      have h1 : sigma10^[1] m = sigma10 m := rfl
      rw [h1] at hkm
      exact absurd hkm hne
    | succ j =>
      have h2 : sigma10^[j + 1 + 1] m = sigma10^[j + 1] (sigma10 m) :=
        Function.iterate_succ_apply _ _ _
      rw [h2] at hkm
      exact reach_ge (m := sigma10 m) ⟨j + 1, Nat.le_add_left 1 j, hkm⟩

/-- Every iterate preserves the value mod 9. -/
theorem modEq_iterate (m : ℕ) : ∀ k : ℕ, m ≡ sigma10^[k] m [MOD 9] := by
  intro k
  induction k with
  | zero => rfl
  | succ k ih =>
    rw [Function.iterate_succ_apply']
    exact ih.trans (Nat.modEq_nine_digits_sum _)

theorem reach_modEq {n m : ℕ} (h : reachesDigitSum n m) : m ≡ n [MOD 9] := by
  obtain ⟨k, -, hkm⟩ := h
  rw [← hkm]
  exact modEq_iterate m k

theorem reach_sigma_modEq {n m : ℕ} (h : reachesDigitSum n m) :
    sigma10 m ≡ n [MOD 9] :=
  (Nat.modEq_nine_digits_sum m).symm.trans (reach_modEq h)

/-! ## Length bounds for digit sums -/

theorem eighteen_mul_lt_pow {d : ℕ} (h : 3 ≤ d) : 18 * d < 10 ^ (d - 1) := by
  induction d, h using Nat.le_induction with
  | base => norm_num
  | succ d hd ih =>
    have hexp : d + 1 - 1 = d - 1 + 1 := by omega
    rw [hexp, pow_succ']
    have h1 : 9 ≤ 9 * 10 ^ (d - 1) := by
      have h2 : (10 : ℕ) ^ 2 ≤ 10 ^ (d - 1) :=
        Nat.pow_le_pow_right (by norm_num) (by omega)
      norm_num at h2
      omega
    omega

theorem nine_mul_succ_lt_pow {d : ℕ} (h : 3 ≤ d) :
    9 * (d + 1) < 10 ^ (d - 1) := by
  induction d, h using Nat.le_induction with
  | base => norm_num
  | succ d hd ih =>
    have hexp : d + 1 - 1 = d - 1 + 1 := by omega
    rw [hexp, pow_succ']
    have h1 : 9 ≤ 9 * 10 ^ (d - 1) := by
      have h2 : (10 : ℕ) ^ 2 ≤ 10 ^ (d - 1) :=
        Nat.pow_le_pow_right (by norm_num) (by omega)
      norm_num at h2
      omega
    omega

/-- For `10 ≤ n`, `n ≠ 19`, twice the digit sum does not exceed `n`. -/
theorem two_sigma_le {n : ℕ} (hn : 10 ≤ n) (hn19 : n ≠ 19) :
    2 * sigma10 n ≤ n := by
  rcases lt_or_ge (Nat.digits 10 n).length 3 with hlen | hlen
  · have hn100 : n < 100 := by
      have hlt : n < 10 ^ (Nat.digits 10 n).length :=
        Nat.lt_base_pow_length_digits (by norm_num : (1 : ℕ) < 10)
      have h2 : (Nat.digits 10 n).length ≤ 2 := by omega
      calc n < 10 ^ (Nat.digits 10 n).length := hlt
        _ ≤ 10 ^ 2 := Nat.pow_le_pow_right (by norm_num) h2
        _ = 100 := by norm_num
    obtain ⟨u, t, hu, ht1, ht9, hnut⟩ :
        ∃ u t : ℕ, u < 10 ∧ 1 ≤ t ∧ t < 10 ∧ n = u + 10 * t :=
      ⟨n % 10, n / 10, Nat.mod_lt _ (by norm_num), by omega, by omega,
        (Nat.mod_add_div n 10).symm⟩
    have hn_eq : Nat.digits 10 n = [u, t] := by
      have hmod : n % 10 = u := by omega
      have hdiv : n / 10 = t := by omega
      have hd : Nat.digits 10 n = (n % 10) :: Nat.digits 10 (n / 10) :=
        Nat.digits_def' (by norm_num) (by omega)
      rw [hd, hmod, hdiv, Nat.digits_of_lt 10 t (by omega) ht9]
    have hsum : sigma10 n = u + t := by
      show (Nat.digits 10 n).sum = u + t
      rw [hn_eq]
      rfl
    by_cases ha2 : 2 ≤ t
    · rw [hsum]
      omega
    · have ha1 : t = 1 := by omega
      have hu9 : u ≠ 9 := by
        intro h9
        apply hn19
        omega
      rw [hsum]
      omega
  · have hle : 2 * (Nat.digits 10 n).sum ≤ 18 * (Nat.digits 10 n).length := by
      have hs := sum_le_nine_mul_len n
      simp only [sigma10] at hs
      omega
    have hpow : 18 * (Nat.digits 10 n).length <
        10 ^ ((Nat.digits 10 n).length - 1) := eighteen_mul_lt_pow hlen
    have hbase : 10 ^ ((Nat.digits 10 n).length - 1) ≤ n :=
      pow10_pred_len_le (by omega : n ≠ 0)
    show 2 * (Nat.digits 10 n).sum ≤ n
    omega

/-- `n = 2σ n` forces `n = 18` for `n ≥ 10`. -/
theorem eq_18_of_two_sigma {n : ℕ} (hn : 10 ≤ n) (h : n = 2 * sigma10 n) :
    n = 18 := by
  have h' : n = 2 * (Nat.digits 10 n).sum := h
  rcases lt_or_ge (Nat.digits 10 n).length 3 with hlen | hlen
  · have hn100 : n < 100 := by
      have hlt : n < 10 ^ (Nat.digits 10 n).length :=
        Nat.lt_base_pow_length_digits (by norm_num : (1 : ℕ) < 10)
      have h2 : (Nat.digits 10 n).length ≤ 2 := by omega
      calc n < 10 ^ (Nat.digits 10 n).length := hlt
        _ ≤ 10 ^ 2 := Nat.pow_le_pow_right (by norm_num) h2
        _ = 100 := by norm_num
    obtain ⟨u, t, hu, ht1, ht9, hnut⟩ :
        ∃ u t : ℕ, u < 10 ∧ 1 ≤ t ∧ t < 10 ∧ n = u + 10 * t :=
      ⟨n % 10, n / 10, Nat.mod_lt _ (by norm_num), by omega, by omega,
        (Nat.mod_add_div n 10).symm⟩
    have hn_eq : Nat.digits 10 n = [u, t] := by
      have hmod : n % 10 = u := by omega
      have hdiv : n / 10 = t := by omega
      have hd : Nat.digits 10 n = (n % 10) :: Nat.digits 10 (n / 10) :=
        Nat.digits_def' (by norm_num) (by omega)
      rw [hd, hmod, hdiv, Nat.digits_of_lt 10 t (by omega) ht9]
    have hsum : sigma10 n = u + t := by
      show (Nat.digits 10 n).sum = u + t
      rw [hn_eq]
      rfl
    omega
  · exfalso
    have hle : 2 * (Nat.digits 10 n).sum ≤ 18 * (Nat.digits 10 n).length := by
      have hs := sum_le_nine_mul_len n
      simp only [sigma10] at hs
      omega
    have hpow : 18 * (Nat.digits 10 n).length <
        10 ^ ((Nat.digits 10 n).length - 1) := eighteen_mul_lt_pow hlen
    have hbase : 10 ^ ((Nat.digits 10 n).length - 1) ≤ n :=
      pow10_pred_len_le (by omega : n ≠ 0)
    omega

theorem sigma10_add9_lt {n : ℕ} (hn : 11 ≤ n) : sigma10 (n + 9) < n := by
  by_cases h27 : n ≤ 27
  · interval_cases n <;> decide
  · simp only [not_le] at h27
    have hnp : n < 10 ^ (Nat.digits 10 n).length :=
      Nat.lt_base_pow_length_digits (by norm_num : (1 : ℕ) < 10)
    have h9d : n + 9 < 10 ^ ((Nat.digits 10 n).length + 1) := by
      have hp : 1 ≤ (10 : ℕ) ^ (Nat.digits 10 n).length :=
        Nat.one_le_pow _ _ (by norm_num)
      calc n + 9 < 10 ^ (Nat.digits 10 n).length + 9 := by omega
        _ ≤ 10 ^ (Nat.digits 10 n).length +
              9 * 10 ^ (Nat.digits 10 n).length := by
            apply Nat.add_le_add_left
            exact Nat.le_mul_of_pos_right 9 hp
        _ = 10 ^ ((Nat.digits 10 n).length + 1) := by rw [pow_succ']; ring
    have hlen9 : (Nat.digits 10 (n + 9)).length ≤
        (Nat.digits 10 n).length + 1 := by
      rw [Nat.digits_length_le_iff (by norm_num : (1 : ℕ) < 10)]
      exact h9d
    have hsle : sigma10 (n + 9) ≤ 9 * ((Nat.digits 10 n).length + 1) := by
      have h := sum_le_nine_mul_len (n + 9)
      simp only [sigma10] at h
      simp only [sigma10]
      omega
    rcases lt_or_ge (Nat.digits 10 n).length 3 with hlen | hlen
    · have h100 : n < 100 := by
        have hlt : n < 10 ^ (Nat.digits 10 n).length :=
          Nat.lt_base_pow_length_digits (by norm_num : (1 : ℕ) < 10)
        have h2 : (Nat.digits 10 n).length ≤ 2 := by omega
        calc n < 10 ^ (Nat.digits 10 n).length := hlt
          _ ≤ 10 ^ 2 := Nat.pow_le_pow_right (by norm_num) h2
          _ = 100 := by norm_num
      omega
    · have hpow : 9 * ((Nat.digits 10 n).length + 1) <
          10 ^ ((Nat.digits 10 n).length - 1) := nine_mul_succ_lt_pow hlen
      have hbase : 10 ^ ((Nat.digits 10 n).length - 1) ≤ n :=
        pow10_pred_len_le (by omega : n ≠ 0)
      omega

theorem sigma10_le_18_of_le_198 {x : ℕ} (h : x ≤ 198) : sigma10 x ≤ 18 := by
  by_cases hx2 : x ≤ 99
  · have hlen : (Nat.digits 10 x).length ≤ 2 := by
      rw [Nat.digits_length_le_iff (by norm_num : (1 : ℕ) < 10)]
      have : (10 : ℕ) ^ 2 = 100 := by norm_num
      omega
    have hsle := sum_le_nine_mul_len x
    simp only [sigma10] at hsle
    simp only [sigma10]
    omega
  · simp only [not_le] at hx2
    have hlen : (Nat.digits 10 x).length = 3 := by
      have hge : 2 < (Nat.digits 10 x).length :=
        (Nat.lt_digits_length_iff (by norm_num : (1 : ℕ) < 10) x).mpr (by
          have : (10 : ℕ) ^ 2 = 100 := by norm_num
          omega)
      have hle : (Nat.digits 10 x).length ≤ 3 := by
        rw [Nat.digits_length_le_iff (by norm_num : (1 : ℕ) < 10)]
        have : (10 : ℕ) ^ 3 = 1000 := by norm_num
        omega
      omega
    obtain ⟨u, t, c, hutc⟩ := List.length_eq_three.mp hlen
    have hx_eq : x = u + 10 * t + 100 * c := by
      have h' := Nat.ofDigits_digits 10 x
      rw [hutc, Nat.ofDigits_cons, Nat.ofDigits_cons, Nat.ofDigits_cons,
        Nat.ofDigits_nil] at h'
      omega
    have hub : u < 10 := Nat.digits_lt_base (by norm_num) (by
      rw [hutc]; simp)
    have htb : t < 10 := Nat.digits_lt_base (by norm_num) (by
      rw [hutc]; simp)
    have hcb : c < 10 := Nat.digits_lt_base (by norm_num) (by
      rw [hutc]; simp)
    have hsum : (Nat.digits 10 x).sum = u + t + c := by
      rw [hutc]
      simp only [List.sum_cons, List.sum_nil]
      omega
    have hs : sigma10 x = u + t + c := hsum
    omega

/-- If `sigma10 (sigma10 m) ≥ 19` then `sigma10 m ≥ 199` (a value `≤ 198`
has digit sum `≤ 18`). -/
theorem ge_199_of_sigma_ge {m : ℕ} (h : 19 ≤ sigma10 (sigma10 m)) :
    199 ≤ sigma10 m := by
  by_contra hlt
  simp only [not_le] at hlt
  have h18 := sigma10_le_18_of_le_198 (by omega : sigma10 m ≤ 198)
  omega

/-! ## Palindrome structure lemmas -/

/-- A palindromic `m` that begins with `n` and is "long" decomposes as
`digits m = digits n.reverse ++ mid ++ digits n` with `mid` a palindrome. -/
theorem pal_decomp {n m : ℕ} (hpal : isPalindrome10 m)
    (hbg : beginsWith10 n m)
    (hlen : 2 * (Nat.digits 10 n).length ≤ (Nat.digits 10 m).length) :
    ∃ mid : List ℕ, Nat.digits 10 m =
      (Nat.digits 10 n).reverse ++ mid ++ Nat.digits 10 n ∧
      mid.Palindrome := by
  obtain ⟨X, hX⟩ := hbg
  have hXlen : X.length =
      (Nat.digits 10 m).length - (Nat.digits 10 n).length := by
    have h' := congrArg List.length hX
    simp only [List.length_append] at h'
    omega
  have hXle : (Nat.digits 10 n).length ≤ X.length := by omega
  have hrev : (Nat.digits 10 n).reverse ++ X.reverse =
      X ++ Nat.digits 10 n := by
    have h := hpal.reverse_eq
    rw [← hX, List.reverse_append] at h
    exact h
  have hpre : (Nat.digits 10 n).reverse =
      X.take (Nat.digits 10 n).length := by
    have h := congrArg (List.take (Nat.digits 10 n).length) hrev
    rw [List.take_left' (by simp : (Nat.digits 10 n).reverse.length =
        (Nat.digits 10 n).length)] at h
    rw [List.take_append_of_le_length hXle] at h
    exact h
  refine ⟨X.drop (Nat.digits 10 n).length, ?_, ?_⟩
  · conv_lhs => rw [← hX, ← X.take_append_drop (Nat.digits 10 n).length, ← hpre]
  · have hXde : X = (Nat.digits 10 n).reverse ++
        X.drop (Nat.digits 10 n).length := by
      conv_lhs => rw [← X.take_append_drop (Nat.digits 10 n).length, ← hpre]
    rw [hXde, List.reverse_append] at hrev
    simp only [List.reverse_reverse, ← List.append_assoc] at hrev
    have h1 : (Nat.digits 10 n).reverse ++
        (X.drop (Nat.digits 10 n).length).reverse =
        (Nat.digits 10 n).reverse ++ X.drop (Nat.digits 10 n).length :=
      (List.append_left_inj _).mp hrev
    have h2 : (X.drop (Nat.digits 10 n).length).reverse =
        X.drop (Nat.digits 10 n).length := (List.append_right_inj _).mp h1
    exact List.Palindrome.of_reverse_eq h2

/-- A palindromic `m` that begins with `n` but is "short": the overlap
forces `sigma10 m + s0 = 2 * sigma10 n` with `s0` bounded below by the
leading digit of `n`. -/
theorem pal_decomp_short {n m : ℕ} (hpal : isPalindrome10 m)
    (hbg : beginsWith10 n m)
    (hlen : (Nat.digits 10 m).length < 2 * (Nat.digits 10 n).length) :
    ∃ s0 : ℕ, n % 10 ≤ s0 ∧ sigma10 m + s0 = 2 * sigma10 n := by
  obtain ⟨X, hX⟩ := hbg
  have hXlen : X.length =
      (Nat.digits 10 m).length - (Nat.digits 10 n).length := by
    have h' := congrArg List.length hX
    simp only [List.length_append] at h'
    omega
  have hXlt : X.length < (Nat.digits 10 n).length := by omega
  have hrev : (Nat.digits 10 n).reverse ++ X.reverse =
      X ++ Nat.digits 10 n := by
    have h := hpal.reverse_eq
    rw [← hX, List.reverse_append] at h
    exact h
  set j := (Nat.digits 10 n).length - X.length with hj
  have hdn_eq : Nat.digits 10 n =
      ((Nat.digits 10 n).take j).reverse ++ X.reverse := by
    have h := congrArg (List.drop X.length) hrev
    rw [List.drop_left] at h
    rw [List.drop_append_of_le_length (by
        rw [List.length_reverse]; exact hXlt.le :
        X.length ≤ (Nat.digits 10 n).reverse.length)] at h
    rw [List.drop_reverse] at h
    rw [← hj] at h
    exact h.symm
  have hdn_ne : Nat.digits 10 n ≠ [] := by
    intro h0
    rw [h0] at hXlt
    simp at hXlt
  have hs0 : n % 10 ≤ ((Nat.digits 10 n).take j).sum := by
    have hA_ne : ((Nat.digits 10 n).take j).reverse ≠ [] := by
      intro h0
      have h0' : (Nat.digits 10 n).take j = [] :=
        List.reverse_eq_nil_iff.mp h0
      have hjl : ((Nat.digits 10 n).take j).length = j := by
        rw [List.length_take]
        omega
      rw [h0', List.length_nil] at hjl
      omega
    obtain ⟨b, bs, hbs⟩ := List.exists_cons_of_ne_nil hA_ne
    have hb_memA : b ∈ (Nat.digits 10 n).take j :=
      List.mem_reverse.mp (by rw [hbs]; exact List.mem_cons_self)
    have hnx : n % 10 = b := by
      have hd : Nat.digits 10 n = (n % 10) :: Nat.digits 10 (n / 10) :=
        Nat.digits_def' (by norm_num)
          (Nat.pos_of_ne_zero (Nat.digits_ne_nil_iff_ne_zero.mp hdn_ne))
      rw [hdn_eq, hbs] at hd
      exact (List.cons.inj hd).1.symm
    exact hnx ▸ List.le_sum_of_mem hb_memA
  have hsm : sigma10 m + ((Nat.digits 10 n).take j).sum =
      2 * sigma10 n := by
    have h1 : (Nat.digits 10 m).sum =
        X.sum + (Nat.digits 10 n).sum := by
      have h' := congrArg List.sum hX
      rw [List.sum_append] at h'
      exact h'.symm
    have h2 : (Nat.digits 10 n).sum =
        ((Nat.digits 10 n).take j).sum + X.sum := by
      have h' := congrArg List.sum hdn_eq
      rwa [List.sum_append, List.sum_reverse, List.sum_reverse] at h'
    show (Nat.digits 10 m).sum + ((Nat.digits 10 n).take j).sum =
      2 * (Nat.digits 10 n).sum
    omega
  exact ⟨((Nat.digits 10 n).take j).sum, hs0, hsm⟩

/-- An odd-length palindrome splits as `A ++ [c] ++ A.reverse`. -/
theorem pal_odd_split {M : List ℕ} (hpal : M.Palindrome) {k : ℕ}
    (hlen : M.length = 2 * k + 1) :
    ∃ A : List ℕ, ∃ c : ℕ, M = A ++ [c] ++ A.reverse ∧ A.length = k := by
  have hk : k < M.length := by omega
  refine ⟨M.take k, M[k]'hk, ?_, ?_⟩
  · have h1 : M = M.take (k + 1) ++ M.drop (k + 1) :=
      (M.take_append_drop (k + 1)).symm
    have h2 : M.take (k + 1) = M.take k ++ [M[k]'hk] :=
      List.take_succ_eq_append_getElem hk
    have h3 : M.drop (k + 1) = (M.take k).reverse := by
      conv_lhs => rw [← hpal.reverse_eq]
      rw [List.drop_reverse, hlen, show 2 * k + 1 - (k + 1) = k from by omega]
    conv_lhs => rw [h1]
    rw [h2, h3]
  · rw [List.length_take]
    omega

/-- An even-length palindrome splits as `A ++ A.reverse`. -/
theorem pal_even_split {M : List ℕ} (hpal : M.Palindrome) {k : ℕ}
    (hlen : M.length = 2 * k) :
    ∃ A : List ℕ, M = A ++ A.reverse ∧ A.length = k := by
  have hdrop : M.drop k = (M.take k).reverse := by
    conv_lhs => rw [← hpal.reverse_eq]
    rw [List.drop_reverse, hlen, show 2 * k - k = k from by omega]
  refine ⟨M.take k, ?_, ?_⟩
  · conv_lhs => rw [← M.take_append_drop k]
    rw [hdrop]
  · rw [List.length_take]
    omega

theorem sum_even_of_pal_even {M : List ℕ} (hpal : M.Palindrome) {k : ℕ}
    (hlen : M.length = 2 * k) : Even M.sum := by
  obtain ⟨A, hA, -⟩ := pal_even_split hpal hlen
  rw [hA, List.sum_append, List.sum_reverse]
  exact ⟨A.sum, rfl⟩

theorem odd_len_of_odd_sum {M : List ℕ} (hpal : M.Palindrome)
    (hodd : Odd M.sum) : Odd M.length := by
  rcases Nat.even_or_odd M.length with he | ho
  · obtain ⟨k, hk⟩ := he
    have hs : Even M.sum := sum_even_of_pal_even hpal (k := k) (by omega)
    obtain ⟨r, hr⟩ := hs
    obtain ⟨r', hr'⟩ := hodd
    omega
  · exact ho

theorem all_eq_9_of_sum : ∀ {l : List ℕ}, (∀ d ∈ l, d < 10) →
    l.sum = 9 * l.length → ∀ d ∈ l, d = 9 := by
  intro l
  induction l with
  | nil => simp
  | cons x xs ih =>
    intro hd hsum d hd'
    rw [List.sum_cons, List.length_cons] at hsum
    have hx : x < 10 := hd x List.mem_cons_self
    have hxs : ∀ d ∈ xs, d < 10 := fun e he => hd e (List.mem_cons_of_mem _ he)
    rcases Nat.lt_or_ge x 9 with hx9 | hx9
    · have hle : xs.sum ≤ 9 * xs.length := list_sum_le_nine hxs
      omega
    · have hxv : x = 9 := by omega
      have hsum' : xs.sum = 9 * xs.length := by omega
      rw [List.mem_cons] at hd'
      rcases hd' with rfl | hd'
      · exact hxv
      · exact ih hxs hsum' d hd'

/-- If `sigma10 m = n` is forced to be `2σn + s0` with `s0 > 0`,
`m` cannot be a short palindrome beginning with `n`. -/
theorem short_sigma_lt {n m : ℕ} (hn : 10 ≤ n) (hn19 : n ≠ 19)
    (hpal : isPalindrome10 m) (hbg : beginsWith10 n m)
    (hlen : (Nat.digits 10 m).length < 2 * (Nat.digits 10 n).length) :
    sigma10 m < n := by
  obtain ⟨s0, hs0, hsum⟩ := pal_decomp_short hpal hbg hlen
  have htn : 2 * sigma10 n ≤ n := two_sigma_le hn hn19
  rcases lt_or_eq_of_le (show sigma10 m ≤ n by omega) with hlt | heq
  · exact hlt
  · exfalso
    have hs0z : s0 = 0 := by omega
    have h2 : n = 2 * sigma10 n := by omega
    have h18 : n = 18 := eq_18_of_two_sigma hn h2
    rw [h18] at hs0
    omega

/-! ## Palindromic digit strings -/

/-- A (non-palindromic) digit string of length `k` and sum `s`, when
`s ≤ 9k`. -/
theorem digit_string_of_sum : ∀ (k s : ℕ), s ≤ 9 * k →
    ∃ A : List ℕ, A.length = k ∧ (∀ d ∈ A, d < 10) ∧ A.sum = s
  | 0, s, h => ⟨[], rfl, fun d hd => by simp at hd, by
      have hs : s = 0 := by omega
      simp [hs]⟩
  | k + 1, s, h => by
    obtain ⟨A, hAlen, hAd, hAsum⟩ :=
      digit_string_of_sum k (s - min 9 s) (by omega)
    refine ⟨min 9 s :: A, by simp [hAlen], ?_, ?_⟩
    · intro d hd'
      simp only [List.mem_cons] at hd'
      rcases hd' with rfl | hd'
      · omega
      · exact hAd d hd'
    · rw [List.sum_cons, hAsum, Nat.add_sub_cancel' (Nat.min_le_right 9 s)]

theorem even_pal_string {t L : ℕ} (ht : Even t) (hL : Even L)
    (hcap : t ≤ 9 * L) :
    ∃ M : List ℕ, isPalDigitString L t M := by
  obtain ⟨k, hk⟩ := hL
  obtain ⟨r, hr⟩ := ht
  obtain ⟨A, hAlen, hAd, hAsum⟩ := digit_string_of_sum k (t / 2) (by omega)
  refine ⟨A ++ A.reverse, ?_, ?_, ?_, ?_⟩
  · simp only [List.length_append, List.length_reverse, hAlen]
    omega
  · intro d hd
    simp only [List.mem_append, List.mem_reverse] at hd
    rcases hd with hd | hd
    · exact hAd d hd
    · exact hAd d hd
  · exact List.Palindrome.append_reverse A
  · simp only [List.sum_append, List.sum_reverse, hAsum]
    omega

theorem odd_pal_string {t L : ℕ} (hL : Odd L) (hcap : t ≤ 9 * L) :
    ∃ M : List ℕ, isPalDigitString L t M := by
  obtain ⟨k, hk⟩ := hL
  obtain ⟨A, hAlen, hAd, hAsum⟩ :=
    digit_string_of_sum k (min (t / 2) (9 * k)) (by omega)
  refine ⟨A ++ [t - 2 * A.sum] ++ A.reverse, ?_, ?_, ?_, ?_⟩
  · simp only [List.length_append, List.length_reverse, List.length_singleton,
      hAlen]
    omega
  · intro d hd
    simp only [List.mem_append, List.mem_singleton, List.mem_reverse] at hd
    rcases hd with (hd | hde) | hd
    · exact hAd d hd
    · rw [hde]
      have hc9 : t - 2 * A.sum ≤ 9 := by omega
      omega
    · exact hAd d hd
  · apply List.Palindrome.of_reverse_eq
    simp [List.reverse_append]
  · simp only [List.sum_append, List.sum_reverse, List.sum_singleton, hAsum]
    omega

/-- Existence of a palindromic digit-string of sum `t` of length at most
`⌈t/9⌉ + 1`. -/
theorem pal_string (t : ℕ) :
    ∃ l : ℕ, l ≤ (t + 8) / 9 + 1 ∧ ∃ M : List ℕ, isPalDigitString l t M := by
  set c := (t + 8) / 9 with hc
  have hcap : t ≤ 9 * c := by omega
  by_cases hte : Even t
  · rcases Nat.even_or_odd c with hco | hco
    · obtain ⟨M, hM⟩ := even_pal_string hte hco hcap
      exact ⟨c, by omega, M, hM⟩
    · have hc1 : Even (c + 1) := by
        obtain ⟨r, hr⟩ := hco
        exact ⟨r + 1, by omega⟩
      obtain ⟨M, hM⟩ := even_pal_string hte hc1 (show t ≤ 9 * (c + 1) by omega)
      exact ⟨c + 1, by omega, M, hM⟩
  · rcases Nat.even_or_odd c with hco | hco
    · have hc1 : Odd (c + 1) := by
        obtain ⟨r, hr⟩ := hco
        exact ⟨r, by omega⟩
      obtain ⟨M, hM⟩ := odd_pal_string hc1 (show t ≤ 9 * (c + 1) by omega)
      exact ⟨c + 1, by omega, M, hM⟩
    · obtain ⟨M, hM⟩ := odd_pal_string hco hcap
      exact ⟨c, by omega, M, hM⟩

theorem lmin_spec (t : ℕ) : ∃ M : List ℕ, isPalDigitString (lmin t) t M := by
  show lmin t ∈ {l : ℕ | ∃ M : List ℕ, isPalDigitString l t M}
  apply Nat.sInf_mem
  obtain ⟨l, -, M, hM⟩ := pal_string t
  exact ⟨l, M, hM⟩

theorem lmin_le {t l : ℕ} (h : ∃ M : List ℕ, isPalDigitString l t M) :
    lmin t ≤ l :=
  Nat.sInf_le h

theorem lmin_le_ceil (t : ℕ) : lmin t ≤ (t + 8) / 9 + 1 := by
  obtain ⟨l, hle, M, hspec⟩ := pal_string t
  calc lmin t ≤ l := lmin_le ⟨M, hspec⟩
    _ ≤ (t + 8) / 9 + 1 := hle

theorem gmid_spec {l t : ℕ} (h : ∃ M : List ℕ, isPalDigitString l t M) :
    isPalDigitString l t (gmid l t) := by
  have hne : {v : ℕ | ∃ M : List ℕ, isPalDigitString l t M ∧
      Nat.ofDigits 10 M = v}.Nonempty := by
    obtain ⟨M, hM⟩ := h
    exact ⟨Nat.ofDigits 10 M, M, hM, rfl⟩
  have hg : gmid l t = Classical.choose (Nat.sInf_mem hne) := dite_eq_left h
  rw [hg]
  exact (Classical.choose_spec (Nat.sInf_mem hne)).1

/-- `gmid` is `Nat.ofDigits`-minimal among palindromic digit strings of the
same length and sum. -/
theorem ofDigits_gmid_le {l t : ℕ} (h : ∃ M : List ℕ, isPalDigitString l t M)
    {mid : List ℕ} (hmid : isPalDigitString l t mid) :
    Nat.ofDigits 10 (gmid l t) ≤ Nat.ofDigits 10 mid := by
  have hne : {v : ℕ | ∃ M : List ℕ, isPalDigitString l t M ∧
      Nat.ofDigits 10 M = v}.Nonempty :=
    ⟨Nat.ofDigits 10 mid, mid, hmid, rfl⟩
  have hmem : Nat.ofDigits 10 mid ∈ {v : ℕ | ∃ M : List ℕ,
      isPalDigitString l t M ∧ Nat.ofDigits 10 M = v} :=
    ⟨mid, hmid, rfl⟩
  have hg : gmid l t = Classical.choose (Nat.sInf_mem hne) := dite_eq_left h
  have hspec := Classical.choose_spec (Nat.sInf_mem hne)
  rw [hg, hspec.2]
  exact Nat.sInf_le hmem

/-- `digits 10 (ofDigits 10 L) = L` for the concatenated digit string. -/
theorem digits_concat {n : ℕ} (hn0 : n ≠ 0) {M : List ℕ}
    (hMd : ∀ d ∈ M, d < 10) :
    Nat.digits 10 (Nat.ofDigits 10 ((Nat.digits 10 n).reverse ++ M ++
      Nat.digits 10 n)) =
      (Nat.digits 10 n).reverse ++ M ++ Nat.digits 10 n := by
  apply Nat.digits_ofDigits 10 (by norm_num)
  · intro d hd
    rw [List.mem_append, List.mem_append, List.mem_reverse] at hd
    rcases hd with (hd | hd) | hd
    · exact Nat.digits_lt_base (by norm_num) hd
    · exact hMd d hd
    · exact Nat.digits_lt_base (by norm_num) hd
  · intro h
    have hdn_ne : Nat.digits 10 n ≠ [] :=
      Nat.digits_ne_nil_iff_ne_zero.mpr hn0
    rw [List.getLast_append_of_ne_nil _ hdn_ne]
    exact Nat.getLast_digit_ne_zero 10 hn0

/-! ## The witness -/

/-- Digit sum of the canonical witness equals `n`. -/
theorem witness_sigma {n : ℕ} (hn : 10 ≤ n) (hn19 : n ≠ 19) :
    sigma10 (Nat.ofDigits 10 ((Nat.digits 10 n).reverse ++
        gmid (lmin (n - 2 * sigma10 n)) (n - 2 * sigma10 n) ++
        Nat.digits 10 n)) = n := by
  set t := n - 2 * sigma10 n with ht
  set W := Nat.ofDigits 10 ((Nat.digits 10 n).reverse ++
    gmid (lmin t) t ++ Nat.digits 10 n) with hW
  have htn : 2 * sigma10 n ≤ n := two_sigma_le hn hn19
  have hn0 : n ≠ 0 := by omega
  have hMspec := gmid_spec (lmin_spec t)
  have hWdig : Nat.digits 10 W =
      (Nat.digits 10 n).reverse ++ gmid (lmin t) t ++ Nat.digits 10 n :=
    digits_concat hn0 hMspec.2.1
  show (Nat.digits 10 W).sum = n
  rw [hWdig, List.sum_append, List.sum_append, List.sum_reverse,
    hMspec.2.2.2]
  have ht' : t = n - 2 * (Nat.digits 10 n).sum := ht
  have htn' : 2 * (Nat.digits 10 n).sum ≤ n := htn
  omega

/-- The canonical witness satisfies the three A082935 predicates. -/
theorem witness_mem {n : ℕ} (hn : 10 ≤ n) (hn19 : n ≠ 19) :
    isPalindrome10 (Nat.ofDigits 10 ((Nat.digits 10 n).reverse ++
        gmid (lmin (n - 2 * sigma10 n)) (n - 2 * sigma10 n) ++
        Nat.digits 10 n)) ∧
    beginsWith10 n (Nat.ofDigits 10 ((Nat.digits 10 n).reverse ++
        gmid (lmin (n - 2 * sigma10 n)) (n - 2 * sigma10 n) ++
        Nat.digits 10 n)) ∧
    reachesDigitSum n (Nat.ofDigits 10 ((Nat.digits 10 n).reverse ++
        gmid (lmin (n - 2 * sigma10 n)) (n - 2 * sigma10 n) ++
        Nat.digits 10 n)) := by
  set t := n - 2 * sigma10 n with ht
  set W := Nat.ofDigits 10 ((Nat.digits 10 n).reverse ++
    gmid (lmin t) t ++ Nat.digits 10 n) with hW
  have htn : 2 * sigma10 n ≤ n := two_sigma_le hn hn19
  have hn0 : n ≠ 0 := by omega
  have hMspec := gmid_spec (lmin_spec t)
  have hWdig : Nat.digits 10 W =
      (Nat.digits 10 n).reverse ++ gmid (lmin t) t ++ Nat.digits 10 n :=
    digits_concat hn0 hMspec.2.1
  refine ⟨?_, ?_, ?_⟩
  · rw [isPalindrome10, hWdig]
    apply List.Palindrome.of_reverse_eq
    rw [List.reverse_append, List.reverse_append, hMspec.2.2.1.reverse_eq,
      List.reverse_reverse, ← List.append_assoc]
  · rw [beginsWith10, hWdig]
    exact ⟨(Nat.digits 10 n).reverse ++ gmid (lmin t) t, rfl⟩
  · exact ⟨1, le_refl 1, witness_sigma hn hn19⟩

/-- The canonical witness is minimal: every palindrome beginning with `n`
whose digit-sum orbit reaches `n` is at least the witness. -/
theorem witness_min {n m : ℕ} (hn : 10 ≤ n) (hn19 : n ≠ 19)
    (hpal : isPalindrome10 m) (hbg : beginsWith10 n m)
    (hreach : reachesDigitSum n m) :
    Nat.ofDigits 10 ((Nat.digits 10 n).reverse ++
        gmid (lmin (n - 2 * sigma10 n)) (n - 2 * sigma10 n) ++
        Nat.digits 10 n) ≤ m := by
  set t := n - 2 * sigma10 n with ht
  set W := Nat.ofDigits 10 ((Nat.digits 10 n).reverse ++
    gmid (lmin t) t ++ Nat.digits 10 n) with hW
  have htn : 2 * sigma10 n ≤ n := two_sigma_le hn hn19
  have hn0 : n ≠ 0 := by omega
  have hMspec := gmid_spec (lmin_spec t)
  have hWdig : Nat.digits 10 W =
      (Nat.digits 10 n).reverse ++ gmid (lmin t) t ++ Nat.digits 10 n :=
    digits_concat hn0 hMspec.2.1
  -- length ≥ 2|dn| case: palindrome decomposition
  rcases lt_or_ge (Nat.digits 10 m).length (2 * (Nat.digits 10 n).length)
    with hshort | hlong
  · -- short: sigma10 m < n contradicts reach_ge
    exfalso
    have hlt := short_sigma_lt hn hn19 hpal hbg hshort
    have hge := reach_ge hreach
    omega
  · obtain ⟨mid, hmid, hpmid⟩ := pal_decomp hpal hbg hlong
    have hmidD : ∀ d ∈ mid, d < 10 := by
      intro d hd
      apply Nat.digits_lt_base (by norm_num : (1 : ℕ) < 10)
      rw [hmid, List.mem_append, List.mem_append]
      exact Or.inl (Or.inr hd)
    have hsm : sigma10 m = 2 * sigma10 n + mid.sum := by
      have hsum_eq : (Nat.digits 10 m).sum =
          ((Nat.digits 10 n).reverse ++ mid ++ Nat.digits 10 n).sum :=
        congrArg List.sum hmid
      simp only [List.sum_append, List.sum_reverse] at hsum_eq
      show (Nat.digits 10 m).sum = 2 * (Nat.digits 10 n).sum + mid.sum
      omega
    have hs_ge : t ≤ mid.sum := by
      have hge := reach_ge hreach
      rw [hsm] at hge
      omega
    have hsm9 : mid.sum % 9 = t % 9 := by
      have hmod : sigma10 m ≡ n [MOD 9] := reach_sigma_modEq hreach
      have hmod' : sigma10 m % 9 = n % 9 := hmod
      omega
    -- the ofDigits comparison W ≤ m reduces to the inner comparison
    have hmval : m = Nat.ofDigits 10 ((Nat.digits 10 n).reverse ++ mid ++
        Nat.digits 10 n) := by
      have h' := Nat.ofDigits_digits 10 m
      rw [hmid] at h'
      exact h'.symm
    rw [hmval]
    show Nat.ofDigits 10 ((Nat.digits 10 n).reverse ++ gmid (lmin t) t ++
        Nat.digits 10 n) ≤
      Nat.ofDigits 10 ((Nat.digits 10 n).reverse ++ mid ++ Nat.digits 10 n)
    rw [Nat.ofDigits_append, Nat.ofDigits_append, Nat.ofDigits_digits,
      Nat.ofDigits_append, Nat.ofDigits_append, Nat.ofDigits_digits,
      List.length_append, List.length_append, hMspec.1]
    -- goal: ofD dn.rev + 10^|dn.rev|·ofD gmid + 10^(|dn.rev|+lmin)·n ≤
    --       ofD dn.rev + 10^|dn.rev|·ofD mid + 10^(|dn.rev|+|mid|)·n
    have hgn : Nat.ofDigits 10 (gmid (lmin t) t) < 10 ^ (lmin t) := by
      have h := Nat.ofDigits_lt_base_pow_length (b := 10) (by norm_num)
        hMspec.2.1
      rwa [hMspec.1] at h
    have hl9 : 9 * lmin t ≤ t + 17 := by
      have hl := lmin_le_ceil t
      omega
    -- inner comparison (the `10^|dn.rev|` factor lifts it to the goal)
    have key : Nat.ofDigits 10 (gmid (lmin t) t) + 10 ^ lmin t * n ≤
        Nat.ofDigits 10 mid + 10 ^ mid.length * n := by
      rcases lt_or_ge mid.length (lmin t) with hlt | hge
      · -- |mid| < lmin: mid.sum = t forced → exact witness shorter than lmin
        exfalso
        have hle9 : mid.sum ≤ 9 * mid.length := list_sum_le_nine hmidD
        have hseq : mid.sum = t := by omega
        have := lmin_le ⟨mid, rfl, hmidD, hpmid, hseq⟩
        omega
      · rcases eq_or_lt_of_le hge with hEq | hgt
        · -- |mid| = lmin: mid.sum ∈ {t, t+9}
          rw [← hEq]
          rcases Nat.lt_or_ge t mid.sum with hsum_gt | hsum_eq'
          · -- mid.sum > t → mid.sum = t + 9 → sigma10 m = n + 9
            exfalso
            have hs9 : mid.sum = t + 9 := by
              have hle9 : mid.sum ≤ 9 * mid.length := list_sum_le_nine hmidD
              omega
            have hσm : sigma10 m = n + 9 := by omega
            rcases lt_or_ge n 11 with hn10 | hn11
            · -- n < 11 → n = 10: mid.sum = 17 odd → |mid| odd → lmin = 1 → sum ≤ 9
              have hn_eq : n = 10 := by omega
              have hσ10 : sigma10 10 = 1 := by decide
              have ht8 : t = 8 := by
                rw [hn_eq, hσ10] at ht
                omega
              have hsum17 : mid.sum = 17 := by omega
              have hodd_sum : Odd mid.sum := ⟨8, by omega⟩
              have hodd_len : Odd mid.length := odd_len_of_odd_sum hpmid hodd_sum
              have hceil := lmin_le_ceil t
              have hlm1 : lmin t = 1 := by
                have ho : Odd (lmin t) := by rwa [← hEq] at hodd_len
                obtain ⟨r, hr⟩ := ho
                omega
              have hle9 : mid.sum ≤ 9 * mid.length := list_sum_le_nine hmidD
              omega
            · -- 11 ≤ n: sigma10 m = n + 9 contradicts reach2_ge + sigma10_add9_lt
              have hlt9 := sigma10_add9_lt hn11
              have hge2 := reach2_ge hreach (by omega : sigma10 m ≠ n)
              have h2 : sigma10^[2] m = sigma10 (sigma10 m) := rfl
              rw [h2, hσm] at hge2
              omega
          · -- mid.sum = t: mid is a t-witness → ofDigits_gmid_le
            have hseq : mid.sum = t := by omega
            apply Nat.add_le_add_right
            exact ofDigits_gmid_le ⟨mid, hEq.symm, hmidD, hpmid, hseq⟩
              ⟨hEq.symm, hmidD, hpmid, hseq⟩
        · -- |mid| > lmin: the weight of 10^|mid|·n dominates
          have hpow : 10 ^ (lmin t + 1) ≤ 10 ^ mid.length :=
            Nat.pow_le_pow_right (by norm_num) (by omega)
          have h1 : Nat.ofDigits 10 (gmid (lmin t) t) +
              10 ^ lmin t * n < 10 ^ lmin t + 10 ^ lmin t * n := by
            have h' := add_lt_add_right hgn (10 ^ lmin t * n)
            omega
          have h2 : 10 ^ lmin t + 10 ^ lmin t * n =
              10 ^ lmin t * (n + 1) := by ring
          have h3 : 10 ^ lmin t * (n + 1) ≤ 10 ^ (lmin t + 1) * n := by
            rw [pow_succ']
            have hn1 : n + 1 ≤ 10 * n := by omega
            have hm := Nat.mul_le_mul_left (10 ^ lmin t) hn1
            rwa [show (10 : ℕ) * 10 ^ lmin t * n =
              10 ^ lmin t * (10 * n) from by ring]
          have h4 : 10 ^ (lmin t + 1) * n ≤ 10 ^ mid.length * n :=
            Nat.mul_le_mul_right n hpow
          have h5 : 10 ^ lmin t ≤ 10 ^ mid.length :=
            Nat.pow_le_pow_right (by norm_num) (by omega)
          omega
    -- lift `key` by the `10^|dn.rev|` factor
    have hBC : 10 ^ (Nat.digits 10 n).reverse.length *
          Nat.ofDigits 10 (gmid (lmin t) t) +
        10 ^ ((Nat.digits 10 n).reverse.length + lmin t) * n ≤
        10 ^ (Nat.digits 10 n).reverse.length * Nat.ofDigits 10 mid +
        10 ^ ((Nat.digits 10 n).reverse.length + mid.length) * n := by
      have h' := Nat.mul_le_mul_left (10 ^ (Nat.digits 10 n).reverse.length) key
      rw [Nat.left_distrib, Nat.left_distrib, ← Nat.mul_assoc, ← pow_add,
        ← Nat.mul_assoc, ← pow_add] at h'
      exact h'
    rw [Nat.add_assoc, Nat.add_assoc]
    exact Nat.add_le_add_left hBC _

/-- Upper bound part of the formula. -/
theorem a082935_eq_w {n : ℕ} (hn : 10 ≤ n) (hn19 : n ≠ 19) :
    a082935 n = Nat.ofDigits 10 ((Nat.digits 10 n).reverse ++
        gmid (lmin (n - 2 * sigma10 n)) (n - 2 * sigma10 n) ++
        Nat.digits 10 n) := by
  set t := n - 2 * sigma10 n with ht
  set W := Nat.ofDigits 10 ((Nat.digits 10 n).reverse ++
    gmid (lmin t) t ++ Nat.digits 10 n) with hW
  have hmem : isPalindrome10 W ∧ beginsWith10 n W ∧ reachesDigitSum n W :=
    witness_mem hn hn19
  have hmin : isPalindrome10 (a082935 n) ∧ beginsWith10 n (a082935 n) ∧
      reachesDigitSum n (a082935 n) :=
    Nat.sInf_mem (s := {m : ℕ | isPalindrome10 m ∧ beginsWith10 n m ∧
      reachesDigitSum n m}) ⟨W, hmem⟩
  exact le_antisymm (Nat.sInf_le (s := {m : ℕ | isPalindrome10 m ∧
      beginsWith10 n m ∧ reachesDigitSum n m}) hmem)
    (by
      have := witness_min hn hn19 hmin.1 hmin.2.1 hmin.2.2
      rwa [← hW] at this)

/-- For `n ≤ 9`, `n` itself is the smallest member. -/
theorem a082935_eq_self_of_lt10 {n : ℕ} (hn : n ≤ 9) : a082935 n = n := by
  have hn10 : n < 10 := by omega
  have hmem : n ∈ {m : ℕ | isPalindrome10 m ∧ beginsWith10 n m ∧
      reachesDigitSum n m} := by
    refine ⟨?_, ?_, 1, le_refl 1, ?_⟩
    · rcases Nat.eq_zero_or_pos n with rfl | hp
      · exact List.Palindrome.nil
      · rw [isPalindrome10, Nat.digits_of_lt 10 n (by omega) hn10]
        exact List.Palindrome.singleton n
    · exact ⟨[], by simp⟩
    · show sigma10 n = n
      exact sigma10_eq_self hn10
  have hmin : isPalindrome10 (a082935 n) ∧ beginsWith10 n (a082935 n) ∧
      reachesDigitSum n (a082935 n) := Nat.sInf_mem ⟨n, hmem⟩
  have hge : n ≤ a082935 n := by
    rcases lt_or_ge (a082935 n) n with hlt | hge
    · exfalso
      have hle : n ≤ sigma10 (a082935 n) := reach_ge hmin.2.2
      rw [sigma10_eq_self (by omega : a082935 n < 10)] at hle
      omega
    · exact hge
  exact le_antisymm (Nat.sInf_le hmem) hge

/-- For `n ≤ 9`, `a082217 n = n` too. -/
theorem a082217_eq_self_of_lt10 {n : ℕ} (hn : n ≤ 9) : a082217 n = n := by
  have hn10 : n < 10 := by omega
  have hmem : n ∈ {m : ℕ | isPalindrome10 m ∧ beginsWith10 n m ∧
      sigma10 m = n} := by
    refine ⟨?_, ?_, ?_⟩
    · rcases Nat.eq_zero_or_pos n with rfl | hp
      · exact List.Palindrome.nil
      · rw [isPalindrome10, Nat.digits_of_lt 10 n (by omega) hn10]
        exact List.Palindrome.singleton n
    · exact ⟨[], by simp⟩
    · exact sigma10_eq_self hn10
  have hmin : isPalindrome10 (a082217 n) ∧ beginsWith10 n (a082217 n) ∧
      sigma10 (a082217 n) = n := Nat.sInf_mem ⟨n, hmem⟩
  have hge : n ≤ a082217 n := by
    rcases lt_or_ge (a082217 n) n with hlt | hge
    · exfalso
      have hle := hmin.2.2
      rw [sigma10_eq_self (by omega : a082217 n < 10)] at hle
      omega
    · exact hge
  exact le_antisymm (Nat.sInf_le hmem) hge

/-- `n = 19` has no palindrome beginning with `19` whose digit sum is `19`. -/
theorem a082217_19 : a082217 19 = 0 := by
  have hd19 : Nat.digits 10 19 = [9, 1] := by decide
  have h19len : (Nat.digits 10 19).length = 2 := by decide
  have hσ19 : sigma10 19 = 10 := by decide
  have h0 : {m : ℕ | isPalindrome10 m ∧ beginsWith10 19 m ∧
      sigma10 m = 19} = ∅ := by
    apply Set.eq_empty_of_forall_notMem
    intro m hm
    obtain ⟨hpal, hbg, hsm⟩ := hm
    rcases lt_or_ge (Nat.digits 10 m).length 4 with hlen | hlen
    · obtain ⟨s0, hs0, hsum⟩ := pal_decomp_short hpal hbg (by
        rw [h19len]; omega)
      rw [hσ19] at hsum
      omega
    · obtain ⟨mid, hmid, -⟩ := pal_decomp hpal hbg (by
        rw [h19len]; omega)
      have hsm' : (Nat.digits 10 m).sum = 20 + mid.sum := by
        have hsum_eq : (Nat.digits 10 m).sum =
            ((Nat.digits 10 19).reverse ++ mid ++ Nat.digits 10 19).sum :=
          congrArg List.sum hmid
        rw [hd19] at hsum_eq
        have hrev : [9, 1].reverse = ([1, 9] : List ℕ) := by decide
        rw [hrev] at hsum_eq
        simp only [List.sum_append, List.sum_cons, List.sum_nil] at hsum_eq
        omega
      have hσm : sigma10 m = 20 + mid.sum := hsm'
      omega
  rw [a082217, h0]
  exact Nat.sInf_empty

/-- `a082217 n = a082935 n` for `n ≥ 1`, `n ≠ 19`. -/
theorem a082217_eq_a082935 {n : ℕ} (hn : 1 ≤ n) (hn19 : n ≠ 19) :
    a082217 n = a082935 n := by
  rcases lt_or_ge n 10 with hlt | hge
  · rw [a082935_eq_self_of_lt10 (by omega), a082217_eq_self_of_lt10 (by omega)]
  · set t := n - 2 * sigma10 n with ht
    set W := Nat.ofDigits 10 ((Nat.digits 10 n).reverse ++
      gmid (lmin t) t ++ Nat.digits 10 n) with hW
    have hWmem := witness_mem hge hn19
    have hWmem' : isPalindrome10 W ∧ beginsWith10 n W ∧ sigma10 W = n :=
      ⟨hWmem.1, hWmem.2.1, witness_sigma hge hn19⟩
    have hmin' : isPalindrome10 (a082217 n) ∧ beginsWith10 n (a082217 n) ∧
        sigma10 (a082217 n) = n :=
      Nat.sInf_mem (s := {m : ℕ | isPalindrome10 m ∧ beginsWith10 n m ∧
        sigma10 m = n}) ⟨W, hWmem'⟩
    rw [a082935_eq_w hge hn19]
    exact le_antisymm (Nat.sInf_le (s := {m : ℕ | isPalindrome10 m ∧
        beginsWith10 n m ∧ sigma10 m = n}) hWmem')
      (by
        have hr : reachesDigitSum n (a082217 n) :=
          ⟨1, le_refl 1, hmin'.2.2⟩
        have := witness_min hge hn19 hmin'.1 hmin'.2.1 hr
        rwa [← hW] at this)

/-- `a082217 n = 0 ↔ n = 19` for `n ≥ 1`. -/
theorem a082217_eq_zero_iff {n : ℕ} (hn : 1 ≤ n) :
    a082217 n = 0 ↔ n = 19 := by
  constructor
  · intro h
    by_contra h19
    rw [a082217_eq_a082935 hn h19] at h
    rcases lt_or_ge n 10 with hlt | hge
    · rw [a082935_eq_self_of_lt10 (by omega)] at h
      omega
    · rw [a082935_eq_w hge h19] at h
      have hbgW : beginsWith10 n (Nat.ofDigits 10 ((Nat.digits 10 n).reverse ++
          gmid (lmin (n - 2 * sigma10 n)) (n - 2 * sigma10 n) ++
          Nat.digits 10 n)) := (witness_mem hge h19).2.1
      rw [h] at hbgW
      have hdn_ne : Nat.digits 10 n ≠ [] :=
        Nat.digits_ne_nil_iff_ne_zero.mpr (by omega)
      have hll : (Nat.digits 10 n).length ≤ ([] : List ℕ).length := by
        have := hbgW.length_le
        rwa [Nat.digits_zero] at this
      simp only [List.length_nil, Nat.le_zero] at hll
      exact hdn_ne (List.length_eq_zero_iff.mp hll)
  · intro h
    rw [h]
    exact a082217_19

/-! ## The `n = 19` witness -/

/-- The 21-digit palindromic middle of the `n = 19` witness. -/
def mid19 : List ℕ := [4] ++ List.replicate 19 9 ++ [4]

/-- The 25-digit little-endian digit list of `1949999999999999999999491`. -/
def L19 : List ℕ :=
  [1, 9] ++ [4] ++ List.replicate 19 9 ++ [4] ++ [9, 1]

theorem W19_eq : Nat.ofDigits 10 L19 = 1949999999999999999999491 := by decide

theorem L19_digits : Nat.digits 10 1949999999999999999999491 = L19 := by
  have h := Nat.digits_ofDigits 10 (by norm_num) L19 (by decide) (by decide)
  rw [W19_eq] at h
  exact h

theorem mid19_spec : isPalDigitString 21 179 mid19 := by
  refine ⟨by decide, by decide, by decide, by decide⟩

theorem W19_sigma : sigma10 1949999999999999999999491 = 199 := by
  rw [show sigma10 1949999999999999999999491 =
      (Nat.digits 10 1949999999999999999999491).sum from rfl, L19_digits]
  decide

theorem W19_sigma2 : sigma10^[2] 1949999999999999999999491 = 19 := by
  rw [show sigma10^[2] 1949999999999999999999491 =
      sigma10 (sigma10 1949999999999999999999491) from rfl, W19_sigma]
  decide

theorem W19_mem : isPalindrome10 1949999999999999999999491 ∧
    beginsWith10 19 1949999999999999999999491 ∧
    reachesDigitSum 19 1949999999999999999999491 := by
  refine ⟨?_, ?_, ?_⟩
  · rw [isPalindrome10, L19_digits]
    decide
  · rw [beginsWith10, L19_digits]
    have hd19 : Nat.digits 10 19 = [9, 1] := by decide
    rw [hd19]
    exact ⟨[1, 9] ++ [4] ++ List.replicate 19 9 ++ [4], by decide⟩
  · exact ⟨2, by norm_num, W19_sigma2⟩

theorem ofDigits_mid19_lt : Nat.ofDigits 10 mid19 < 5 * 10 ^ 20 := by
  have hsplit : mid19 = ([4] ++ List.replicate 19 9) ++ [4] := by
    simp only [mid19]
  have hlen : ([4] ++ List.replicate 19 9).length = 20 := by
    decide
  rw [hsplit, Nat.ofDigits_append, Nat.ofDigits_singleton, hlen]
  have hlt : Nat.ofDigits 10 ([4] ++ List.replicate 19 9) < 10 ^ 20 := by
    have h := Nat.ofDigits_lt_base_pow_length (b := 10) (by norm_num)
      (l := [4] ++ List.replicate 19 9) (by decide)
    rwa [hlen] at h
  calc Nat.ofDigits 10 ([4] ++ List.replicate 19 9) + 10 ^ 20 * 4
      < 10 ^ 20 + 10 ^ 20 * 4 := Nat.add_lt_add_right hlt _
    _ = 5 * 10 ^ 20 := by ring

/-- Any 21-digit palindrome with digit sum 179 either is `mid19` or has
`ofDigits ≥ 5·10²⁰` (its first/last digit ≥ 5). -/
theorem mid21_cases {mid : List ℕ} (hlen : mid.length = 21)
    (hpal : mid.Palindrome) (hsum : mid.sum = 179)
    (hd : ∀ d ∈ mid, d < 10) :
    mid = mid19 ∨ 5 * 10 ^ 20 ≤ Nat.ofDigits 10 mid := by
  obtain ⟨A, c, hA, hAlen⟩ := pal_odd_split hpal (k := 10) hlen
  obtain ⟨a, ar, har⟩ := List.exists_cons_of_ne_nil (l := A) (by
    intro h0
    rw [h0] at hAlen
    simp at hAlen)
  have ha : a < 10 := hd a (by rw [hA, har]; simp)
  have hc : c < 10 := hd c (by rw [hA]; simp)
  have harD : ∀ d ∈ ar, d < 10 := fun d hd' => hd d (by
    have h1 : d ∈ A := by rw [har]; exact List.mem_cons_of_mem _ hd'
    rw [hA]
    exact List.mem_append_left _ (List.mem_append_left _ h1))
  have hAr : ar.length = 9 := by
    have := hAlen
    rw [har, List.length_cons] at this
    omega
  have hsumA : A.sum = a + ar.sum := by rw [har]; simp
  have hsum_eq : mid.sum = 2 * A.sum + c := by
    rw [hA]
    simp only [List.sum_append, List.sum_reverse, List.sum_cons, List.sum_nil,
      add_zero]
    omega
  have ha4 : 4 ≤ a := by
    have hrest : ar.sum ≤ 9 * ar.length := list_sum_le_nine harD
    omega
  rcases eq_or_lt_of_le ha4 with ha4eq | ha5
  · left
    have hrest9 : ∀ d ∈ ar, d = 9 :=
      all_eq_9_of_sum harD (by
        have hrest : ar.sum ≤ 9 * ar.length := list_sum_le_nine harD
        omega)
    have hA' : A = [4] ++ List.replicate 9 9 := by
      have har9 : ar = List.replicate 9 9 := by
        rw [List.eq_replicate_iff]
        exact ⟨hAr, hrest9⟩
      rw [har, ha4eq, har9, List.singleton_append]
    have hc9 : c = 9 := by
      have h85 : ([4] ++ List.replicate 9 9).sum = 85 := by decide
      rw [hA'] at hsum_eq
      rw [h85] at hsum_eq
      omega
    rw [hA, hA', hc9]
    decide
  · right
    have hgl : mid = (a :: ar ++ [c] ++ ar.reverse) ++ [a] := by
      rw [hA, har, List.reverse_cons]
      simp only [List.cons_append, ← List.append_assoc]
    rw [hgl, Nat.ofDigits_append, Nat.ofDigits_singleton]
    have hi_len : (a :: ar ++ [c] ++ ar.reverse).length = 20 := by
      rw [List.length_append, List.length_append, List.length_cons,
        List.length_singleton, List.length_reverse, hAr]
    rw [hi_len]
    have h5 : 5 * 10 ^ 20 ≤ 10 ^ 20 * a := by
      calc 5 * 10 ^ 20 ≤ a * 10 ^ 20 := Nat.mul_le_mul_right _ ha5
        _ = 10 ^ 20 * a := by ring
    omega

/-- `sigma10 (sigma10 W19) = 19` reaches `19` at stage 2. -/
theorem W19_min {m : ℕ} (hpal : isPalindrome10 m)
    (hbg : beginsWith10 19 m) (hreach : reachesDigitSum 19 m) :
    (1949999999999999999999491 : ℕ) ≤ m := by
  have hd19 : Nat.digits 10 19 = [9, 1] := by decide
  have h19len : (Nat.digits 10 19).length = 2 := by decide
  have hσ19 : sigma10 19 = 10 := by decide
  rcases lt_or_ge (Nat.digits 10 m).length 4 with hlen | hlen
  · exfalso
    obtain ⟨s0, hs0, hsum⟩ := pal_decomp_short hpal hbg (by
      rw [h19len]; omega)
    have hge := reach_ge hreach
    rw [hσ19] at hsum
    omega
  · obtain ⟨mid, hmid, hpmid⟩ := pal_decomp hpal hbg (by
      rw [h19len]; omega)
    have hmidD : ∀ d ∈ mid, d < 10 := by
      intro d hd
      apply Nat.digits_lt_base (by norm_num : (1 : ℕ) < 10)
      rw [hmid, List.mem_append, List.mem_append]
      exact Or.inl (Or.inr hd)
    have hsm : sigma10 m = 20 + mid.sum := by
      have hsum_eq : (Nat.digits 10 m).sum =
          ((Nat.digits 10 19).reverse ++ mid ++ Nat.digits 10 19).sum :=
        congrArg List.sum hmid
      rw [hd19] at hsum_eq
      have hrev : [9, 1].reverse = ([1, 9] : List ℕ) := by decide
      rw [hrev] at hsum_eq
      simp only [List.sum_append, List.sum_cons, List.sum_nil] at hsum_eq
      have hsm' : (Nat.digits 10 m).sum = 20 + mid.sum := by omega
      exact hsm'
    have hne : sigma10 m ≠ 19 := by omega
    have hge2 : 19 ≤ sigma10^[2] m := reach2_ge hreach hne
    have h2 : sigma10^[2] m = sigma10 (sigma10 m) := rfl
    rw [h2] at hge2
    have hge199 : 199 ≤ sigma10 m := ge_199_of_sigma_ge hge2
    have hmid_len20 : 20 ≤ mid.length := by
      have := list_sum_le_nine hmidD
      omega
    have hLen : (Nat.digits 10 m).length = 4 + mid.length := by
      rw [hmid, hd19]
      simp only [List.length_append, List.length_cons, List.length_nil,
        List.length_reverse]
      omega
    rcases eq_or_lt_of_le hmid_len20 with h20 | hgt20
    · -- |mid| = 20: mid.sum = 180 → sigma10 m = 200 → sigma10² m = 2 < 19
      exfalso
      have hs180 : mid.sum = 180 := by
        have heven : Even mid.sum := sum_even_of_pal_even hpmid (k := 10)
          (by omega)
        have hle := list_sum_le_nine hmidD
        obtain ⟨r, hr⟩ := heven
        omega
      have hσm : sigma10 m = 200 := by omega
      have h10 : sigma10 200 = 2 := by decide
      rw [hσm, h10] at hge2
      omega
    · rcases eq_or_lt_of_le (by omega : 21 ≤ mid.length) with h21 | hgt22
      · -- |mid| = 21: mid.sum ∈ [179, 189] → sigma10 m ∈ [199, 209] → = 199
        have hs_le : mid.sum ≤ 189 := by
          have := list_sum_le_nine hmidD
          omega
        have hσm : sigma10 m = 199 := by
          have key : ∀ v : ℕ, 199 ≤ v → v ≤ 209 → 19 ≤ sigma10 v →
              v = 199 := by
            intro v hv1 hv2 h19v
            interval_cases v <;> first
              | rfl
              | exact absurd h19v (by decide)
          exact key _ hge199 (by omega) hge2
        have hs179 : mid.sum = 179 := by omega
        rcases mid21_cases h21.symm hpmid hs179 hmidD with hcase | hcase
        · -- mid = mid19 → m = W19
          have hL19 : Nat.digits 10 1949999999999999999999491 =
              (Nat.digits 10 19).reverse ++ mid19 ++ Nat.digits 10 19 := by
            rw [L19_digits, hd19]
            rfl
          have hm_eq : m = 1949999999999999999999491 := by
            have h1 := Nat.ofDigits_digits 10 m
            have h2' := Nat.ofDigits_digits 10 1949999999999999999999491
            rw [hmid, hcase] at h1
            rw [hL19] at h2'
            omega
          omega
        · -- ofDigits mid ≥ 5·10²⁰ → m > W19
          have hge5 : 5 * 10 ^ 20 ≤ Nat.ofDigits 10 mid := hcase
          have hlt19 : Nat.ofDigits 10 mid19 < 5 * 10 ^ 20 := ofDigits_mid19_lt
          have hm_val : m = Nat.ofDigits 10 ((Nat.digits 10 19).reverse ++
              mid ++ Nat.digits 10 19) := by
            have h' := Nat.ofDigits_digits 10 m
            rw [hmid] at h'
            exact h'.symm
          have hW_val : (1949999999999999999999491 : ℕ) =
              Nat.ofDigits 10 ((Nat.digits 10 19).reverse ++ mid19 ++
                Nat.digits 10 19) := by
            have h' := Nat.ofDigits_digits 10 1949999999999999999999491
            have hL19 : Nat.digits 10 1949999999999999999999491 =
                (Nat.digits 10 19).reverse ++ mid19 ++ Nat.digits 10 19 := by
              rw [L19_digits, hd19]
              rfl
            rw [hL19] at h'
            exact h'.symm
          rw [hm_val, hW_val]
          rw [Nat.ofDigits_append, Nat.ofDigits_append, Nat.ofDigits_digits,
            Nat.ofDigits_append, Nat.ofDigits_append, Nat.ofDigits_digits]
          have hrl : ((Nat.digits 10 19).reverse).length = 2 := by
            rw [List.length_reverse, hd19]
            decide
          have hro : Nat.ofDigits 10 ((Nat.digits 10 19).reverse) = 91 := by
            rw [hd19]
            decide
          have hml : mid.length = 21 := h21.symm
          have h19l : mid19.length = 21 := mid19_spec.1
          rw [hro, List.length_append, List.length_append, hrl, hml, h19l]
          have hgm : Nat.ofDigits 10 mid19 ≤ Nat.ofDigits 10 mid :=
            hlt19.le.trans hge5
          exact Nat.add_le_add_right
            (Nat.add_le_add_left (Nat.mul_le_mul_left (10 ^ 2) hgm) 91) _
      · -- |mid| ≥ 22 → m ≥ 10^25 > W19
        have hmne : m ≠ 0 := by
          intro h0
          rw [h0, Nat.digits_zero] at hLen
          simp only [List.length_nil] at hLen
          omega
        have hge : 10 ^ ((Nat.digits 10 m).length - 1) ≤ m :=
          pow10_pred_len_le hmne
        have hlt : (1949999999999999999999491 : ℕ) < 10 ^ 25 := by
          have h := Nat.ofDigits_lt_base_pow_length (b := 10) (by norm_num)
            (l := L19) (by decide)
          rw [show L19.length = 25 from by decide, W19_eq] at h
          exact h
        have hpow : (10 : ℕ) ^ 25 ≤
            10 ^ ((Nat.digits 10 m).length - 1) :=
          Nat.pow_le_pow_right (by norm_num) (by omega)
        omega

theorem a082935_19 : a082935 19 = 1949999999999999999999491 := by
  have hWmem : (1949999999999999999999491 : ℕ) ∈
      {m : ℕ | isPalindrome10 m ∧ beginsWith10 19 m ∧
        reachesDigitSum 19 m} := W19_mem
  have hmin : isPalindrome10 (a082935 19) ∧ beginsWith10 19 (a082935 19) ∧
      reachesDigitSum 19 (a082935 19) := Nat.sInf_mem ⟨_, hWmem⟩
  exact le_antisymm (Nat.sInf_le hWmem)
    (W19_min hmin.1 hmin.2.1 hmin.2.2)

/-! ## Main theorems -/

/-- The exact formula for `a082935` (OEIS %e + Q2). -/
theorem A082935_formula :
    (∀ n : ℕ, 1 ≤ n → n ≤ 9 → a082935 n = n) ∧
    a082935 19 = 1949999999999999999999491 ∧
    (∀ n : ℕ, 10 ≤ n → n ≠ 19 →
      let t := n - 2 * sigma10 n
      a082935 n = Nat.ofDigits 10 ((Nat.digits 10 n).reverse ++
        gmid (lmin t) t ++ Nat.digits 10 n)) := by
  refine ⟨?_, a082935_19, ?_⟩
  · intro n h1 h9
    exact a082935_eq_self_of_lt10 h9
  · intro n h10 h19
    simp only []
    exact a082935_eq_w h10 h19

/-- Robert G. Wilson's conjecture (OEIS %C line), including the `n = 19`
exception where the first-round digit sum is `199` and the second is `19`. -/
theorem A082935_wilson_conjecture :
    (∀ n : ℕ, 1 ≤ n → n ≠ 19 → sigma10 (a082935 n) = n) ∧
    sigma10 (a082935 19) = 199 ∧
    sigma10^[2] (a082935 19) = 19 := by
  refine ⟨?_, ?_, ?_⟩
  · intro n h1 h19
    rcases lt_or_ge n 10 with hlt | hge
    · rw [a082935_eq_self_of_lt10 (by omega)]
      exact sigma10_eq_self (by omega)
    · rw [a082935_eq_w hge h19]
      exact witness_sigma hge h19
  · rw [a082935_19]
    exact W19_sigma
  · rw [a082935_19]
    exact W19_sigma2

/-- The combined A082217 characterization (OEIS %C line):
`a082217 n = 0 ↔ n = 19` and `a082217 n = a082935 n` for `n ≠ 19`. -/
theorem A082217_characterization {n : ℕ} (hn : 1 ≤ n) :
    (a082217 n = 0 ↔ n = 19) ∧ (n ≠ 19 → a082217 n = a082935 n) :=
  ⟨a082217_eq_zero_iff hn, fun h => a082217_eq_a082935 hn h⟩

end

#print axioms a082935_eq_w
#print axioms a082935_19
#print axioms A082935_formula
#print axioms A082935_wilson_conjecture
#print axioms A082217_characterization
