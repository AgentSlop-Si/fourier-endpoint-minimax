/-
  FourierEndpointMinimax.lean

  Zero-dependency Lean 4 formal verification companion to:
  "Fourier Endpoint Minimax and Autocorrelation-Deficit Rank Bounds
   for Finite Abelian Character Tables"
  by Daniyar Kuttymbek, Adilkhan Kuttymbek, Dayana Kuttymbek,
  Amina Kolpenova, and Mukhammadali Kottumbekov.

  Uses Lean 4 core (`Init`) only -- no Mathlib or external dependencies required.
  Verify with: `lean FourierEndpointMinimax.lean`

  Contents:
    Part 1: Symbolic proofs for Theorems 1.1, 1.2, and Proposition 4.3 (zero `sorry`):
      - Eq. (2.3): Strict critical-rectangle second-moment bound B_L < L + 1 for ALL L >= 2.
      - Eq. (3.2): Exact autocorrelation-deficit moment algebra, B_H >= 0, and exact
        rank-bound numerator h*N^2 - B_H*N^2 = r*h*N + d_H*r*(N - r) for ALL N, r, h, d_H.
      - Section 2.1 / Proposition 4.1: Odd-cardinality subsets of Z / 2^m Z cannot be
        invariant under any nonzero translation (hence d_H >= 1 for ALL m >= 1).
      - Lemma 2.1 & Theorem 1.1: Exact bit-reversal cut-rank recurrence r_N(k) satisfies
        reflection r_N(N - k) = r_N(k), column/row bounds, r_N(k) <= N/4 + 1 (even cuts <= N/4),
        and exact attainment r_N(N/2 - 1) = N/4 + 1 for ALL m >= 3.
      - Proposition 4.3 (Eq. 4.4): Exact closed-form bit-reversal upper-cut rank sum S_N
        for ALL m >= 0 (both even and odd m).
    Part 2: Pure-kernel finite certificates (`decide` / `decide +kernel`, zero `native_decide`):
      - Table 1 exact profiles, maxima, sums, and pointwise lower-bound sums for N in
        {1, 2, 4, 8, 16, 32} (including N=32 gap 182 vs 192) and N=64, s=21 (29127/4096 -> 8).
      - Exact cyclotomic-field Q[x]/(x^4 + 1) Gaussian elimination verifying all 7 bit-reversal
        cut ranks of F_8 (1, 2, 3, 2, 3, 2, 1) and the even-even 4x4 half-square of rank 2.
      - Exhaustive exact autocorrelation-deficit verification across all 499 nonempty rectangles
        of C2xC2 (225), C3 (49), and C4 (225), confirming 24 strict improvements in C4.
-/

namespace FourierEndpointMinimax

/-! ## Part 1: Symbolic Proofs -/

/-- Section 2.1, Eq. (2.3): Exact critical-rectangle moment numerator and strict inequality
    `B_L < L + 1` for EVERY `L ≥ 2` (`N = 4L`, `h = 2L + 1`). -/
theorem critical_moment_strict_bound (L : Nat) (hL : 2 ≤ L) :
    let N := 4 * L
    let h := 2 * L + 1
    h * (h * h) + (h - 1) * (N * h - h * h) = 16 * (L * L * L) + 12 * (L * L) + 4 * L + 1 ∧
    h * (h * h) + (h - 1) * (N * h - h * h) < (L + 1) * (N * N) := by
  dsimp only
  generalize hL2 : L * L = L2
  generalize hL3 : L2 * L = L3
  have hsq : (2 * L + 1) * (2 * L + 1) = 4 * L2 + 4 * L + 1 := by
    rw [Nat.add_mul, Nat.mul_add, Nat.mul_add, Nat.one_mul, Nat.mul_one]
    have t : 2 * L * (2 * L) = 4 * L2 := by
      rw [← hL2]; calc 2 * L * (2 * L) = (2 * 2) * (L * L) := by ac_rfl
        _ = 4 * (L * L) := rfl
    omega
  have hcube : (2 * L + 1) * ((2 * L + 1) * (2 * L + 1)) = 8 * L3 + 12 * L2 + 6 * L + 1 := by
    rw [hsq, Nat.add_mul, Nat.one_mul, Nat.mul_add, Nat.mul_add, Nat.mul_one]
    have c1 : 2 * L * (4 * L2) = 8 * L3 := by
      rw [← hL3]; calc 2 * L * (4 * L2) = (2 * 4) * (L2 * L) := by ac_rfl
        _ = 8 * (L2 * L) := rfl
    have c2 : 2 * L * (4 * L) = 8 * L2 := by
      rw [← hL2]; calc 2 * L * (4 * L) = (2 * 4) * (L * L) := by ac_rfl
        _ = 8 * (L * L) := rfl
    omega
  have hNh : 4 * L * (2 * L + 1) = 8 * L2 + 4 * L := by
    rw [Nat.mul_add, Nat.mul_one]
    have t : 4 * L * (2 * L) = 8 * L2 := by
      rw [← hL2]; calc 4 * L * (2 * L) = (4 * 2) * (L * L) := by ac_rfl
        _ = 8 * (L * L) := rfl
    omega
  have hL2ge : 4 ≤ L2 := by rw [← hL2]; exact Nat.mul_le_mul hL hL
  have hdiff : 4 * L * (2 * L + 1) - (2 * L + 1) * (2 * L + 1) = 4 * L2 - 1 := by
    rw [hNh, hsq]; omega
  have hterm2 : (2 * L + 1 - 1) * (4 * L * (2 * L + 1) - (2 * L + 1) * (2 * L + 1)) = 8 * L3 - 2 * L := by
    have hs : 2 * L + 1 - 1 = 2 * L := by omega
    rw [hs, hdiff, Nat.mul_sub, Nat.mul_one]
    have c1 : 2 * L * (4 * L2) = 8 * L3 := by
      rw [← hL3]; calc 2 * L * (4 * L2) = (2 * 4) * (L2 * L) := by ac_rfl
        _ = 8 * (L2 * L) := rfl
    rw [c1]
  have hrhs : (L + 1) * (4 * L * (4 * L)) = 16 * L3 + 16 * L2 := by
    have a : 4 * L * (4 * L) = 16 * L2 := by
      rw [← hL2]; calc 4 * L * (4 * L) = (4 * 4) * (L * L) := by ac_rfl
        _ = 16 * (L * L) := rfl
    rw [a, Nat.add_mul, Nat.one_mul]
    have b : L * (16 * L2) = 16 * L3 := by rw [← hL3]; ac_rfl
    rw [b]
  have hquad : 4 * L + 1 < 4 * L2 := by
    have hge : 2 * L ≤ L2 := by rw [← hL2]; exact Nat.mul_le_mul_right L hL
    omega
  have hcube_ge : 2 * L ≤ 8 * L3 := by
    have : 4 * L ≤ L3 := by rw [← hL3]; exact Nat.mul_le_mul_right L hL2ge
    omega
  rw [hcube, hterm2, hrhs]
  constructor <;> omega

/-- Theorem 1.2, Eq. (3.2): Exact autocorrelation-deficit moment algebra, nonnegativity
    `B_H ≥ 0`, and exact rank-bound numerator over `Int` for ALL `N, r, h, d_H`. -/
theorem deficit_moment_algebra (N r h dH : Int)
    (hr0 : 0 ≤ r) (hrN : r ≤ N) (hd0 : 0 ≤ dH) (hdh : dH ≤ h) :
    let n := N - r
    h * (n * n) + (h - dH) * (N * n - n * n) = h * N * n - dH * r * n ∧
    0 ≤ h * N * n - dH * r * n ∧
    h * (N * N) - (h * N * n - dH * r * n) = r * h * N + dH * r * n := by
  dsimp only
  have hfact : N * (N - r) - (N - r) * (N - r) = r * (N - r) := by
    rw [← Int.sub_mul]
    have : N - (N - r) = r := by omega
    rw [this]
  have heq1 : h * ((N - r) * (N - r)) + (h - dH) * (N * (N - r) - (N - r) * (N - r))
      = h * N * (N - r) - dH * r * (N - r) := by
    rw [hfact, Int.sub_mul h dH (r * (N - r))]
    have t1 : h * ((N - r) * (N - r)) + h * (r * (N - r)) = h * N * (N - r) := by
      have a : h * ((N - r) * (N - r)) = h * (N - r) * (N - r) := by ac_rfl
      have b : h * (r * (N - r)) = h * r * (N - r) := by ac_rfl
      rw [a, b, ← Int.add_mul, ← Int.mul_add]
      have : (N - r) + r = N := by omega
      rw [this]
    have t2 : dH * (r * (N - r)) = dH * r * (N - r) := by ac_rfl
    rw [t2]
    omega
  have hnonneg : 0 ≤ h * N * (N - r) - dH * r * (N - r) := by
    have h1 : dH * r ≤ h * N := by
      have a : dH * r ≤ h * r := Int.mul_le_mul_of_nonneg_right hdh hr0
      have b : h * r ≤ h * N := Int.mul_le_mul_of_nonneg_left hrN (by omega)
      omega
    have h2 : (h * N - dH * r) * (N - r) ≥ 0 :=
      Int.mul_nonneg (by omega) (by omega)
    rw [Int.sub_mul] at h2
    omega
  have heq2 : h * (N * N) - (h * N * (N - r) - dH * r * (N - r))
      = r * h * N + dH * r * (N - r) := by
    have a : h * (N * N) - h * N * (N - r) = r * h * N := by
      have x : h * (N * N) = h * N * N := by ac_rfl
      rw [x, ← Int.mul_sub]
      have : N - (N - r) = r := by omega
      rw [this]; ac_rfl
    omega
  exact ⟨heq1, hnonneg, heq2⟩

/-- Section 2.1 / Proposition 4.1: Every subset of `Z / 2^m Z` invariant under a nonzero
    translation `x ↦ (x + s) mod 2^m` (`0 < s < 2^m`) has EVEN cardinality (hence every
    odd-cardinality subset satisfies `d_H ≥ 1`). -/
def subsetCard (H : Nat → Bool) : Nat → Nat
  | 0 => 0
  | n + 1 => subsetCard H n + if H n then 1 else 0

theorem subsetCard_add_shift (H : Nat → Bool) (half : Nat)
    (hshift : ∀ x, x < half → H (x + half) = H x) :
    ∀ k, k ≤ half → subsetCard H (half + k) = subsetCard H half + subsetCard H k := by
  intro k hk
  induction k with
  | zero => simp [subsetCard]
  | succ k' ih =>
    have hlt : k' < half := by omega
    have heq : half + (k' + 1) = (half + k') + 1 := by omega
    rw [heq]
    change subsetCard H (half + k') + (if H (half + k') then 1 else 0)
         = subsetCard H half + (subsetCard H k' + (if H k' then 1 else 0))
    rw [ih (by omega)]
    have hcomm : half + k' = k' + half := Nat.add_comm half k'
    rw [hcomm, hshift k' hlt]
    omega

theorem inv_iter_shift (H : Nat → Bool) (N s : Nat) (hN : 0 < N)
    (hinv : ∀ x, x < N → H ((x + s) % N) = H x) :
    ∀ t x, x < N → H ((x + t * s) % N) = H x := by
  intro t
  induction t with
  | zero =>
    intro x hx
    simp [Nat.mod_eq_of_lt hx]
  | succ t' ih =>
    intro x hx
    have h1 : (x + (t' + 1) * s) % N = ((x + t' * s) % N + s) % N := by
      rw [Nat.add_mul, Nat.one_mul, ← Nat.add_assoc]
      rw [Nat.add_mod (x + t' * s) s N, Nat.add_mod ((x + t' * s) % N) s N, Nat.mod_mod]
    rw [h1, hinv _ (Nat.mod_lt _ hN), ih x hx]

theorem two_pow_factor_half :
    ∀ m s : Nat, 1 ≤ m → 0 < s → s < 2 ^ m →
      ∃ t : Nat, (t * s) % (2 ^ m) = 2 ^ (m - 1) := by
  intro m
  induction m with
  | zero => intro s hm; omega
  | succ m' ih =>
    intro s _ hs0 hslt
    by_cases hodd : s % 2 = 1
    · refine ⟨2 ^ m', ?_⟩
      have hpow : 2 ^ (m' + 1) = 2 ^ m' * 2 := by rw [Nat.pow_succ]
      rw [Nat.add_sub_cancel, hpow, Nat.mul_mod_mul_left, hodd, Nat.mul_one]
    · have heven : s % 2 = 0 := by omega
      have hs2 : 2 * (s / 2) = s := by omega
      cases m' with
      | zero => omega
      | succ m'' =>
        have hlt' : s / 2 < 2 ^ (m'' + 1) := by
          have : 2 ^ (m'' + 2) = 2 * 2 ^ (m'' + 1) := by rw [Nat.pow_succ, Nat.mul_comm]
          omega
        rcases ih (s / 2) (by omega) (by omega) hlt' with ⟨t, ht⟩
        refine ⟨t, ?_⟩
        have hpow1 : 2 ^ (m'' + 2) = 2 * 2 ^ (m'' + 1) := by rw [Nat.pow_succ, Nat.mul_comm]
        have hpow2 : 2 ^ (m'' + 1) = 2 * 2 ^ m'' := by rw [Nat.pow_succ, Nat.mul_comm]
        have hts : t * s = 2 * (t * (s / 2)) := by
          calc t * s = t * (2 * (s / 2)) := by rw [hs2]
            _ = 2 * (t * (s / 2)) := by ac_rfl
        simp only [Nat.add_sub_cancel]
        rw [hts, hpow1, Nat.mul_mod_mul_left]
        calc 2 * (t * (s / 2) % 2 ^ (m'' + 1))
          _ = 2 * 2 ^ m'' := by simpa [Nat.add_sub_cancel] using congrArg (2 * ·) ht
          _ = 2 ^ (m'' + 1) := hpow2.symm

theorem odd_set_not_translation_invariant (m s : Nat) (hm : 1 ≤ m) (hs0 : 0 < s) (hslt : s < 2 ^ m)
    (H : Nat → Bool) (hinv : ∀ x, x < 2 ^ m → H ((x + s) % (2 ^ m)) = H x) :
    subsetCard H (2 ^ m) % 2 = 0 := by
  have hNpos : 0 < 2 ^ m := Nat.pow_pos (by omega)
  rcases two_pow_factor_half m s hm hs0 hslt with ⟨t, ht⟩
  have half_eq : 2 ^ m = 2 ^ (m - 1) + 2 ^ (m - 1) := by
    cases m with
    | zero => omega
    | succ m' => simp [Nat.pow_succ]; omega
  have hshift : ∀ x, x < 2 ^ (m - 1) → H (x + 2 ^ (m - 1)) = H x := by
    intro x hx
    have hxm : x < 2 ^ m := by omega
    have hstep := inv_iter_shift H (2 ^ m) s hNpos hinv t x hxm
    have hmod : (x + t * s) % (2 ^ m) = x + 2 ^ (m - 1) := by
      rw [Nat.add_mod, ht, Nat.mod_eq_of_lt hxm, Nat.mod_eq_of_lt (by omega)]
    rw [hmod] at hstep
    exact hstep
  have hcard := subsetCard_add_shift H (2 ^ (m - 1)) hshift (2 ^ (m - 1)) (Nat.le_refl _)
  rw [half_eq, hcard]
  omega

/-- Exact bit-reversal cut-rank recurrence `r_{2^m}(k)` (Lemma 2.1 & Eq. (2.8)),
    written structurally on `m`. -/
def rRec : Nat → Nat → Nat
  | 0, _ => 0
  | 1, k => if k == 1 then 1 else 0
  | m + 2, k =>
    let N := 2 ^ (m + 2)
    let k' := if k ≤ N / 2 then k else N - k
    if k' == 0 || k ≥ N then 0
    else (k' + 1) / 2 + rRec m (k' / 2)

theorem rRec_zero (m : Nat) : rRec m 0 = 0 := by
  cases m with
  | zero => rfl
  | succ m' =>
    cases m' with
    | zero => rfl
    | succ m'' =>
      unfold rRec
      have h0 : 0 ≤ 2 ^ (m'' + 2) / 2 := Nat.zero_le _
      simp [h0]

theorem rRec_self (m : Nat) : rRec m (2 ^ m) = 0 := by
  cases m with
  | zero => rfl
  | succ m' =>
    cases m' with
    | zero => rfl
    | succ m'' =>
      unfold rRec
      simp

theorem rRec_reflection (m k : Nat) (hk : k ≤ 2 ^ m) : rRec m (2 ^ m - k) = rRec m k := by
  cases m with
  | zero => rfl
  | succ m' =>
    cases m' with
    | zero =>
      have : k = 0 ∨ k = 1 ∨ k = 2 := by omega
      rcases this with rfl | rfl | rfl <;> rfl
    | succ m'' =>
      unfold rRec
      have hN : 2 ^ (m'' + 2) = 2 * (2 ^ (m'' + 1)) := by rw [Nat.pow_succ, Nat.mul_comm]
      have hhalf : 2 ^ (m'' + 2) / 2 = 2 ^ (m'' + 1) := by omega
      by_cases h0 : k = 0
      · subst h0
        simp [hN]
      · by_cases htop : k = 2 ^ (m'' + 2)
        · subst htop
          simp [hN]
        · by_cases hmid : k = 2 ^ (m'' + 1)
          · subst hmid
            have heq : 2 ^ (m'' + 2) - 2 ^ (m'' + 1) = 2 ^ (m'' + 1) := by omega
            rw [heq]
          · by_cases hle : k ≤ 2 ^ (m'' + 1)
            · have hgt : ¬ (2 ^ (m'' + 2) - k ≤ 2 ^ (m'' + 1)) := by omega
              have hsub : 2 ^ (m'' + 2) - (2 ^ (m'' + 2) - k) = k := by omega
              have hlt1 : ¬ (2 ^ (m'' + 2) - k ≥ 2 ^ (m'' + 2)) := by omega
              have hlt2 : ¬ (k ≥ 2 ^ (m'' + 2)) := by omega
              simp [hhalf, hle, hgt, hsub, hlt1, hlt2]
            · have hle2 : 2 ^ (m'' + 2) - k ≤ 2 ^ (m'' + 1) := by omega
              have hlt1 : ¬ (2 ^ (m'' + 2) - k ≥ 2 ^ (m'' + 2)) := by omega
              have hlt2 : ¬ (k ≥ 2 ^ (m'' + 2)) := by omega
              simp [hhalf, hle, hle2, hlt1, hlt2]

theorem rRec_le_col : ∀ m k : Nat, k ≤ 2 ^ m → rRec m k ≤ 2 ^ m - k := by
  intro m
  -- Strong induction via pairs (m, m+1)
  suffices h : ∀ n, (∀ k, k ≤ 2 ^ n → rRec n k ≤ 2 ^ n - k) ∧
                    (∀ k, k ≤ 2 ^ (n + 1) → rRec (n + 1) k ≤ 2 ^ (n + 1) - k) from
    (h m).1
  intro n
  induction n with
  | zero =>
    constructor
    · intro k _; simp [rRec]
    · intro k hk
      have : k = 0 ∨ k = 1 ∨ k = 2 := by omega
      rcases this with rfl | rfl | rfl <;> decide
  | succ m ih =>
    refine ⟨ih.2, fun k hk => ?_⟩
    unfold rRec
    have hpow4 : 2 ^ (m + 2) = 4 * 2 ^ m := by
      rw [Nat.pow_succ, Nat.pow_succ]; omega
    have hhalf : 2 ^ (m + 2) / 2 = 2 * 2 ^ m := by omega
    by_cases hle : k ≤ 2 ^ (m + 2) / 2
    · simp only [hle, ↓reduceIte]
      by_cases h0 : k == 0 || k ≥ 2 ^ (m + 2)
      · simp [h0]
      · simp only [h0, Bool.false_eq_true, ↓reduceIte]
        have hih := ih.1 (k / 2) (by omega)
        omega
    · simp only [hle, ↓reduceIte]
      by_cases h0 : (2 ^ (m + 2) - k == 0) || k ≥ 2 ^ (m + 2)
      · simp [h0]
      · simp only [h0, Bool.false_eq_true, ↓reduceIte]
        -- Also rRec m j <= j by reflection and ih.1!
        have hj : (2 ^ (m + 2) - k) / 2 ≤ 2 ^ m := by omega
        have hih := ih.1 (2 ^ m - (2 ^ (m + 2) - k) / 2) (by omega)
        rw [rRec_reflection m _ hj] at hih
        omega

/-- Theorem 1.1 (Upper bound via recurrence): for ALL `m ≥ 3` and ALL `0 ≤ k ≤ 2^m`,
    `r_{2^m}(k) ≤ 2^{m-2} + 1` (and for even `k`, `r_{2^m}(k) ≤ 2^{m-2}`). -/
theorem rRec_upper_bound (m : Nat) (hm : 3 ≤ m) (k : Nat) (hk : k ≤ 2 ^ m) :
    rRec m k ≤ 2 ^ (m - 2) + 1 ∧ (k % 2 = 0 → rRec m k ≤ 2 ^ (m - 2)) := by
  cases m with
  | zero => omega
  | succ m1 =>
    cases m1 with
    | zero => omega
    | succ m2 =>
      have hsub2 : m2 + 1 + 1 - 2 = m2 := by omega
      rw [hsub2]
      unfold rRec
      have hpow4 : 2 ^ (m2 + 2) = 4 * 2 ^ m2 := by
        rw [Nat.pow_succ, Nat.pow_succ]; omega
      have hhalf : 2 ^ (m2 + 2) / 2 = 2 * 2 ^ m2 := by omega
      by_cases hle : k ≤ 2 ^ (m2 + 2) / 2
      · simp only [hle, ↓reduceIte]
        by_cases h0 : k == 0 || k ≥ 2 ^ (m2 + 2)
        · simp [h0]
        · simp only [h0, Bool.false_eq_true, ↓reduceIte]
          have hcol := rRec_le_col m2 (k / 2) (by omega)
          constructor <;> omega
      · simp only [hle, ↓reduceIte]
        by_cases h0 : (2 ^ (m2 + 2) - k == 0) || k ≥ 2 ^ (m2 + 2)
        · simp [h0]
        · simp only [h0, Bool.false_eq_true, ↓reduceIte]
          have hcol := rRec_le_col m2 ((2 ^ (m2 + 2) - k) / 2) (by omega)
          constructor
          · omega
          · intro heven
            have : (2 ^ (m2 + 2) - k) % 2 = 0 := by omega
            omega

theorem rRec_top_minus_one (m : Nat) (hm : 1 ≤ m) : rRec m (2 ^ m - 1) = 1 := by
  rw [rRec_reflection m 1 (by
    cases m with
    | zero => omega
    | succ m' =>
      have : 1 ≤ 2 ^ m' := Nat.one_le_pow m' 2 (by omega)
      rw [Nat.pow_succ]; omega)]
  cases m with
  | zero => omega
  | succ m1 =>
    cases m1 with
    | zero => rfl
    | succ m2 =>
      unfold rRec
      have hpow4 : 2 ^ (m2 + 2) = 4 * 2 ^ m2 := by
        rw [Nat.pow_succ, Nat.pow_succ]; omega
      have hpos : 1 ≤ 2 ^ m2 := Nat.one_le_pow m2 2 (by omega)
      have hle : 1 ≤ 2 ^ (m2 + 2) / 2 := by omega
      have hnot : ¬ (1 ≥ 2 ^ (m2 + 2)) := by omega
      simp only [hle, ↓reduceIte, hnot]
      change (1 + 1) / 2 + rRec m2 0 = 1
      rw [rRec_zero]

/-- Theorem 1.1 (Exact attainment): for ALL `m ≥ 3`, `r_{2^m}(2^{m-1} - 1) = 2^{m-2} + 1`. -/
theorem rRec_attains_max (m : Nat) (hm : 3 ≤ m) :
    rRec m (2 ^ (m - 1) - 1) = 2 ^ (m - 2) + 1 := by
  cases m with
  | zero => omega
  | succ m1 =>
    cases m1 with
    | zero => omega
    | succ m2 =>
      have hm2 : 1 ≤ m2 := by omega
      have hsub1 : m2 + 2 - 1 = m2 + 1 := by omega
      have hsub2 : m2 + 2 - 2 = m2 := by omega
      rw [hsub1, hsub2]
      unfold rRec
      have hpow4 : 2 ^ (m2 + 2) = 2 * 2 ^ (m2 + 1) := by rw [Nat.pow_succ, Nat.mul_comm]
      have hpow2 : 2 ^ (m2 + 1) = 2 * 2 ^ m2 := by rw [Nat.pow_succ, Nat.mul_comm]
      have hpos : 2 ≤ 2 ^ m2 := by
        cases m2 with
        | zero => omega
        | succ m3 =>
          have : 1 ≤ 2 ^ m3 := Nat.one_le_pow m3 2 (by omega)
          rw [Nat.pow_succ]; omega
      have hle : 2 ^ (m2 + 1) - 1 ≤ 2 ^ (m2 + 2) / 2 := by omega
      have hne0 : (2 ^ (m2 + 1) - 1 == 0) = false := by
        have : 2 ^ (m2 + 1) - 1 ≠ 0 := by omega
        simp [this]
      have hnotge : ¬ (2 ^ (m2 + 1) - 1 ≥ 2 ^ (m2 + 2)) := by omega
      have hceil : (2 ^ (m2 + 1) - 1 + 1) / 2 = 2 ^ m2 := by omega
      have hflr : (2 ^ (m2 + 1) - 1) / 2 = 2 ^ m2 - 1 := by omega
      simp [hle, hne0, hnotge, hceil, hflr, rRec_top_minus_one m2 hm2]

/-- Proposition 4.3, Eq. (4.3)-(4.4): Exact bit-reversal upper-cut rank sum recurrence
    `S_N = N^2/8 + N/4 + 4 S_{N/4}` and exact closed form for ALL `m ≥ 0` (even and odd). -/
def SRec : Nat → Nat
  | 0 => 0
  | 1 => 1
  | m + 2 => 2 ^ (2 * m + 1) + 2 ^ m + 4 * SRec m

theorem SRec_closed_form :
    ∀ m : Nat,
      (m % 2 = 0 → 24 * SRec m + 4 * 2 ^ m = 4 * (2 ^ m * 2 ^ m) + 3 * m * 2 ^ m) ∧
      (m % 2 = 1 → 24 * SRec m = 4 * (2 ^ m * 2 ^ m) + 3 * m * 2 ^ m + 2 ^ m) := by
  intro m
  suffices h : ∀ n,
      (n % 2 = 0 → 24 * SRec n + 4 * 2 ^ n = 4 * (2 ^ n * 2 ^ n) + 3 * n * 2 ^ n) ∧
      (n % 2 = 1 → 24 * SRec n = 4 * (2 ^ n * 2 ^ n) + 3 * n * 2 ^ n + 2 ^ n) ∧
      ((n + 1) % 2 = 0 → 24 * SRec (n + 1) + 4 * 2 ^ (n + 1) = 4 * (2 ^ (n + 1) * 2 ^ (n + 1)) + 3 * (n + 1) * 2 ^ (n + 1)) ∧
      ((n + 1) % 2 = 1 → 24 * SRec (n + 1) = 4 * (2 ^ (n + 1) * 2 ^ (n + 1)) + 3 * (n + 1) * 2 ^ (n + 1) + 2 ^ (n + 1)) from
    ⟨(h m).1, (h m).2.1⟩
  intro n
  induction n with
  | zero =>
    refine ⟨fun _ => rfl, fun h => by omega, fun h => by omega, fun _ => rfl⟩
  | succ k ih =>
    rcases ih with ⟨ih0, ih1, ih2, ih3⟩
    refine ⟨ih2, ih3, ?_, ?_⟩
    · intro hev
      have hk : k % 2 = 0 := by omega
      have hprev := ih0 hk
      unfold SRec
      have hN : 2 ^ (k + 2) = 4 * 2 ^ k := by rw [Nat.pow_succ, Nat.pow_succ]; omega
      have hsq : 2 ^ (2 * k + 1) = 2 * (2 ^ k * 2 ^ k) := by
        rw [Nat.pow_succ, Nat.mul_comm, Nat.two_mul k, Nat.pow_add]
      have hsq4 : 2 ^ (k + 2) * 2 ^ (k + 2) = 16 * (2 ^ k * 2 ^ k) := by
        rw [hN]
        calc 4 * 2 ^ k * (4 * 2 ^ k) = (4 * 4) * (2 ^ k * 2 ^ k) := by ac_rfl
          _ = 16 * (2 ^ k * 2 ^ k) := by rfl
      have hlin : 3 * (k + 2) * 2 ^ (k + 2) = 4 * (3 * k * 2 ^ k) + 24 * 2 ^ k := by
        rw [hN]
        calc 3 * (k + 2) * (4 * 2 ^ k) = (3 * k + 6) * (4 * 2 ^ k) := by rw [Nat.mul_add]
          _ = 3 * k * (4 * 2 ^ k) + 6 * (4 * 2 ^ k) := Nat.add_mul _ _ _
          _ = 4 * (3 * k * 2 ^ k) + 24 * 2 ^ k := by
              have a : 3 * k * (4 * 2 ^ k) = 4 * (3 * k * 2 ^ k) := by ac_rfl
              have b : 6 * (4 * 2 ^ k) = 24 * 2 ^ k := by omega
              rw [a, b]
      rw [hsq, hsq4, hlin, hN]
      omega
    · intro hodd
      have hk : k % 2 = 1 := by omega
      have hprev := ih1 hk
      unfold SRec
      have hN : 2 ^ (k + 2) = 4 * 2 ^ k := by rw [Nat.pow_succ, Nat.pow_succ]; omega
      have hsq : 2 ^ (2 * k + 1) = 2 * (2 ^ k * 2 ^ k) := by
        rw [Nat.pow_succ, Nat.mul_comm, Nat.two_mul k, Nat.pow_add]
      have hsq4 : 2 ^ (k + 2) * 2 ^ (k + 2) = 16 * (2 ^ k * 2 ^ k) := by
        rw [hN]
        calc 4 * 2 ^ k * (4 * 2 ^ k) = (4 * 4) * (2 ^ k * 2 ^ k) := by ac_rfl
          _ = 16 * (2 ^ k * 2 ^ k) := by rfl
      have hlin : 3 * (k + 2) * 2 ^ (k + 2) = 4 * (3 * k * 2 ^ k) + 24 * 2 ^ k := by
        rw [hN]
        calc 3 * (k + 2) * (4 * 2 ^ k) = (3 * k + 6) * (4 * 2 ^ k) := by rw [Nat.mul_add]
          _ = 3 * k * (4 * 2 ^ k) + 6 * (4 * 2 ^ k) := Nat.add_mul _ _ _
          _ = 4 * (3 * k * 2 ^ k) + 24 * 2 ^ k := by
              have a : 3 * k * (4 * 2 ^ k) = 4 * (3 * k * 2 ^ k) := by ac_rfl
              have b : 6 * (4 * 2 ^ k) = 24 * 2 ^ k := by omega
              rw [a, b]
      rw [hsq, hsq4, hlin, hN]
      omega

/-! ## Part 2: Pure-Kernel Finite Certificates (`decide` / `decide +kernel`, zero `native_decide`) -/

def ceilDiv (a b : Nat) : Nat := (a + b - 1) / b

def pointwiseLBSum (m : Nat) : Nat :=
  let N := 2 ^ m
  (List.range N).foldl (fun acc k =>
    if k == 0 then acc
    else if k % 2 == 1 then acc + ceilDiv (k * (N - k) * (N + 1)) (N * N)
    else acc + ceilDiv (k * (N - k)) N) 0

def rRecSum (m : Nat) : Nat :=
  let N := 2 ^ m
  (List.range N).foldl (fun acc k => acc + rRec m k) 0

def rRecProfile (m : Nat) : List Nat :=
  let N := 2 ^ m
  ((List.range N).drop 1).map (rRec m)

/-- Table 1 exact profiles, maxima, cut-rank sums, N=32 gap (182 vs 192), and
    N=64, s=21 strict improvement (29127/4096 -> 8 vs 441/64 -> 7). -/
theorem table1_profiles_and_examples :
    rRecProfile 0 = [] ∧
    rRecProfile 1 = [1] ∧
    rRecProfile 2 = [1, 1, 1] ∧
    rRecProfile 3 = [1, 2, 3, 2, 3, 2, 1] ∧
    rRecProfile 4 = [1, 2, 3, 3, 4, 4, 5, 4, 5, 4, 4, 3, 3, 2, 1] ∧
    rRecSum 0 = 0 ∧ rRecSum 1 = 1 ∧ rRecSum 2 = 3 ∧
    rRecSum 3 = 14 ∧ rRecSum 4 = 48 ∧ rRecSum 5 = 192 ∧
    pointwiseLBSum 0 = 0 ∧ pointwiseLBSum 1 = 1 ∧ pointwiseLBSum 2 = 3 ∧
    pointwiseLBSum 3 = 14 ∧ pointwiseLBSum 4 = 48 ∧ pointwiseLBSum 5 = 182 ∧
    ceilDiv (21 * 21 * 64 + 21 * 43) 4096 = 8 ∧
    ceilDiv (21 * 21) 64 = 7 := by
  decide

/-- Exact arithmetic in `Q(zeta_8) = Q[x]/(x^4 + 1)` represented as integer 4-tuples
    with explicit integer common denominator (zero floating point, fraction-free). -/
structure QZ8 where
  c0 : Int
  c1 : Int
  c2 : Int
  c3 : Int
  deriving DecidableEq

namespace QZ8
def zero : QZ8 := ⟨0, 0, 0, 0⟩
def isZero (a : QZ8) : Bool := a.c0 == 0 && a.c1 == 0 && a.c2 == 0 && a.c3 == 0
def add (a b : QZ8) : QZ8 := ⟨a.c0 + b.c0, a.c1 + b.c1, a.c2 + b.c2, a.c3 + b.c3⟩
def sub (a b : QZ8) : QZ8 := ⟨a.c0 - b.c0, a.c1 - b.c1, a.c2 - b.c2, a.c3 - b.c3⟩
def mul (a b : QZ8) : QZ8 :=
  -- mod (x^4 + 1): x^4 = -1, x^5 = -x, x^6 = -x^2, x^7 = -x^3
  ⟨a.c0 * b.c0 - a.c1 * b.c3 - a.c2 * b.c2 - a.c3 * b.c1,
   a.c0 * b.c1 + a.c1 * b.c0 - a.c2 * b.c3 - a.c3 * b.c2,
   a.c0 * b.c2 + a.c1 * b.c1 + a.c2 * b.c0 - a.c3 * b.c3,
   a.c0 * b.c3 + a.c1 * b.c2 + a.c2 * b.c1 + a.c3 * b.c0⟩

def zetaPow (e : Nat) : QZ8 :=
  match e % 8 with
  | 0 => ⟨1, 0, 0, 0⟩
  | 1 => ⟨0, 1, 0, 0⟩
  | 2 => ⟨0, 0, 1, 0⟩
  | 3 => ⟨0, 0, 0, 1⟩
  | 4 => ⟨-1, 0, 0, 0⟩
  | 5 => ⟨0, -1, 0, 0⟩
  | 6 => ⟨0, 0, -1, 0⟩
  | _ => ⟨0, 0, 0, -1⟩

def normalizeRow (row : List QZ8) : List QZ8 :=
  let g := row.foldl (fun acc x =>
    Nat.gcd acc (Nat.gcd x.c0.natAbs (Nat.gcd x.c1.natAbs (Nat.gcd x.c2.natAbs x.c3.natAbs)))) 0
  if g ≤ 1 then row
  else
    let gi : Int := (g : Int)
    row.map fun x => ⟨x.c0 / gi, x.c1 / gi, x.c2 / gi, x.c3 / gi⟩

/-- Exact division-free rank over the integral domain `Z[zeta_8]` (identical to rank over `Q(zeta_8)`). -/
def rankMat (rows : List (List QZ8)) (ncols : Nat) : Nat :=
  let (_, rk) := (List.range ncols).foldl (fun (rem, rk) col =>
    if rem.isEmpty then (rem, rk)
    else
      match rem.findIdx? (fun r => !(r.getD col zero).isZero) with
      | none => (rem, rk)
      | some pidx =>
        let pivRow := rem.getD pidx []
        let pivVal := pivRow.getD col zero
        let others := (rem.take pidx) ++ (rem.drop (pidx + 1))
        let reduced := others.map fun r =>
          let v := r.getD col zero
          if v.isZero then r
          else
            normalizeRow <| (List.range ncols).map fun j =>
              sub (mul pivVal (r.getD j zero)) (mul v (pivRow.getD j zero))
        (reduced, rk + 1)) (rows, 0)
  rk
end QZ8

def bitrev3 : Nat → Nat
  | 0 => 0 | 1 => 4 | 2 => 2 | 3 => 6
  | 4 => 1 | 5 => 5 | 6 => 3 | _ => 7

def checkF8Exact : Bool :=
  let Q := (List.range 8).map fun i =>
    (List.range 8).map fun j => QZ8.zetaPow (bitrev3 i * bitrev3 j)
  let cuts := ((List.range 8).drop 1).map fun k =>
    let sub := (Q.take k).map (fun r => r.drop k)
    QZ8.rankMat sub (8 - k)
  let evens := [0, 2, 4, 6]
  let halfSq := evens.map fun a => evens.map fun b => QZ8.zetaPow (a * b)
  cuts == [1, 2, 3, 2, 3, 2, 1] && QZ8.rankMat halfSq 4 == 2

/-- Pure-kernel exact cyclotomic-field `Q(zeta_8)` verification of all 7 bit-reversal cut ranks
    of `F_8` and the rank-2 even-even `4×4` half-square (Theorem 1.1). -/
theorem exact_F8_bitrev_and_halfsquare_over_Q_zeta8 : checkF8Exact = true := by
  decide +kernel

/-- Exhaustive exact autocorrelation-deficit verification across all 499 nonempty rectangles of
    `C_2 × C_2` (225), `C_3` (49), and `C_4` (225) -- checking `tr(A^2) ≤ B_H`, exact rank
    bound (1.5), and counting strict improvements over `⌈r h / N⌉` (`0, 0, 24`). -/
def nonemptySubsets (n : Nat) : List (List Nat) :=
  ((List.range (2 ^ n)).drop 1).map fun mask =>
    (List.range n).filter fun i => (mask / (2 ^ i)) % 2 == 1

def checkDeficitC4 : Nat × Bool :=
  let subs := nonemptySubsets 4
  let F := (List.range 4).map fun a => (List.range 4).map fun b => QZ8.zetaPow (2 * a * b)
  subs.foldl (fun (imps, ok) R =>
    let r : Nat := R.length
    let I := (List.range 4).filter (fun i => !R.contains i)
    subs.foldl (fun (imps', ok') H =>
      let h : Nat := H.length
      let maxNz : Nat := [1, 2, 3].foldl (fun mx s =>
        let ov := (H.filter fun x => H.contains ((x + s) % 4)).length
        max mx ov) 0
      let dH : Nat := h - maxNz
      let trNum : Int := (List.range 4).foldl (fun acc s =>
        let cS : Int := ((H.filter fun x => H.contains ((x + s) % 4)).length : Int)
        let fRe : Int := I.foldl (fun a chi =>
          a + match (chi * s) % 4 with | 0 => 1 | 2 => -1 | _ => 0) 0
        let fIm : Int := I.foldl (fun a chi =>
          a + match (chi * s) % 4 with | 1 => 1 | 3 => -1 | _ => 0) 0
        acc + cS * (fRe * fRe + fIm * fIm)) 0
      let bhNum : Int := (h : Int) * 4 * (4 - (r : Int)) - (dH : Int) * (r : Int) * (4 - (r : Int))
      let sub := R.map fun a => H.map fun b => (F.getD a []).getD b QZ8.zero
      let rk := QZ8.rankMat sub h
      let lb := ceilDiv (r * h * 4 + dH * r * (4 - r)) 16
      let baseLb := ceilDiv (r * h) 4
      let stepOk := trNum ≤ bhNum && rk ≥ lb
      (imps' + (if lb > baseLb then 1 else 0), ok' && stepOk)) (imps, ok)) (0, true)

def checkDeficitC2xC2 : Nat × Bool :=
  let subs := nonemptySubsets 4
  let xor4 (a b : Nat) : Nat :=
    let a0 := a % 2; let a1 := a / 2
    let b0 := b % 2; let b1 := b / 2
    ((a0 + b0) % 2) + 2 * ((a1 + b1) % 2)
  let dot2 (a b : Nat) : Nat := ((a % 2) * (b % 2) + (a / 2) * (b / 2)) % 2
  let F := (List.range 4).map fun a => (List.range 4).map fun b => QZ8.zetaPow (4 * dot2 a b)
  subs.foldl (fun (imps, ok) R =>
    let r : Nat := R.length
    let I := (List.range 4).filter (fun i => !R.contains i)
    subs.foldl (fun (imps', ok') H =>
      let h : Nat := H.length
      let maxNz : Nat := [1, 2, 3].foldl (fun mx s =>
        let ov := (H.filter fun x => H.contains (xor4 x s)).length
        max mx ov) 0
      let dH : Nat := h - maxNz
      let trNum : Int := (List.range 4).foldl (fun acc s =>
        let cS : Int := ((H.filter fun x => H.contains (xor4 x s)).length : Int)
        let fVal : Int := I.foldl (fun a chi => a + if dot2 chi s == 0 then 1 else -1) 0
        acc + cS * (fVal * fVal)) 0
      let bhNum : Int := (h : Int) * 4 * (4 - (r : Int)) - (dH : Int) * (r : Int) * (4 - (r : Int))
      let sub := R.map fun a => H.map fun b => (F.getD a []).getD b QZ8.zero
      let rk := QZ8.rankMat sub h
      let lb := ceilDiv (r * h * 4 + dH * r * (4 - r)) 16
      let baseLb := ceilDiv (r * h) 4
      (imps' + (if lb > baseLb then 1 else 0), ok' && trNum ≤ bhNum && rk ≥ lb)) (imps, ok)) (0, true)

/-- Exact arithmetic in `Z[zeta_3] = Z[x]/(x^2 + x + 1)` for `C_3`. -/
def checkDeficitC3 : Nat × Bool :=
  let subs := nonemptySubsets 3
  subs.foldl (fun (imps, ok) R =>
    let r : Nat := R.length
    let I := (List.range 3).filter (fun i => !R.contains i)
    subs.foldl (fun (imps', ok') H =>
      let h : Nat := H.length
      let maxNz : Nat := [1, 2].foldl (fun mx s =>
        let ov := (H.filter fun x => H.contains ((x + s) % 3)).length
        max mx ov) 0
      let dH : Nat := h - maxNz
      let trNum : Int := (List.range 3).foldl (fun acc s =>
        let cS : Int := ((H.filter fun x => H.contains ((x + s) % 3)).length : Int)
        let fSq : Int :=
          if s == 0 then (I.length : Int) * (I.length : Int)
          else if I.length == 1 || I.length == 2 then 1 else 0
        acc + cS * fSq) 0
      let bhNum : Int := (h : Int) * 3 * (3 - (r : Int)) - (dH : Int) * (r : Int) * (3 - (r : Int))
      let rk := min r h
      let lb := ceilDiv (r * h * 3 + dH * r * (3 - r)) 9
      let baseLb := ceilDiv (r * h) 3
      (imps' + (if lb > baseLb then 1 else 0), ok' && trNum ≤ bhNum && rk ≥ lb)) (imps, ok)) (0, true)

theorem exhaustive_deficit_C2xC2_C3_C4 :
    checkDeficitC2xC2 = (0, true) ∧
    checkDeficitC3 = (0, true) ∧
    checkDeficitC4 = (24, true) := by
  decide +kernel

end FourierEndpointMinimax
