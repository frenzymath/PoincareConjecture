import PoincareConjecture.Proofs.M76.Triangulation.ZeroChargePairedCapStep
import Mathlib.Topology.UnitInterval












set_option autoImplicit false

open Set Geometry

namespace PoincareConjecture.M76.ZeroChargeJoint

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]







theorem HasPairedHeightCap.continue_of_local_steps
    {S C : Set E} (A : E → ℝ) (d : ℝ → Set E) {a b : ℝ} (hab : a ≤ b)
    (hlocal : ∀ c ∈ Icc a b, ∃ ε : ℝ, 0 < ε ∧
      ∀ u v : ℝ, u ∈ Icc a b → v ∈ Icc a b →
        |u - c| ≤ ε → |v - c| ≤ ε → u ≤ v →
        HasPairedHeightCap S C (d u) A u → HasPairedHeightCap S C (d v) A v)
    (hstart : HasPairedHeightCap S C (d a) A a) :
    HasPairedHeightCap S C (d b) A b := by
  classical
  choose ε hε hstep using fun c : Icc a b => hlocal c c.property
  let U : Icc a b → Set (Icc a b) :=
    fun c => {t | (t : ℝ) ∈ Ioo ((c : ℝ) - ε c) ((c : ℝ) + ε c)}
  have hU : ∀ c, IsOpen (U c) := fun _ => isOpen_Ioo.preimage continuous_subtype_val
  have hcover : univ ⊆ ⋃ c, U c := by
    intro t _
    apply mem_iUnion.mpr
    refine ⟨t, ?_⟩
    change (t : ℝ) - ε t < (t : ℝ) ∧ (t : ℝ) < (t : ℝ) + ε t
    constructor <;> linarith [hε t]
  obtain ⟨t, ht0, htmono, ⟨N, htN⟩, hsegment⟩ :=
    exists_monotone_Icc_subset_open_cover_Icc hab hU hcover
  have hcap : ∀ n : ℕ, HasPairedHeightCap S C (d (t n)) A (t n) := by
    intro n
    induction n with
    | zero => simpa only [ht0] using hstart
    | succ n ih =>
      obtain ⟨c, hc⟩ := hsegment n
      have hn : t n ≤ t (n + 1) := htmono (Nat.le_succ n)
      have hleft := hc (left_mem_Icc.mpr hn)
      have hright := hc (right_mem_Icc.mpr hn)
      change (c : ℝ) - ε c < (t n : ℝ) ∧ (t n : ℝ) < (c : ℝ) + ε c at hleft
      change (c : ℝ) - ε c < (t (n + 1) : ℝ) ∧
        (t (n + 1) : ℝ) < (c : ℝ) + ε c at hright
      have hl : |(t n : ℝ) - (c : ℝ)| ≤ ε c :=
        abs_le.mpr ⟨by linarith [hleft.1], by linarith [hleft.2]⟩
      have hr : |(t (n + 1) : ℝ) - (c : ℝ)| ≤ ε c :=
        abs_le.mpr ⟨by linarith [hright.1], by linarith [hright.2]⟩
      exact hstep c (t n) (t (n + 1)) (t n).property (t (n + 1)).property hl hr hn ih
  simpa only [htN N le_rfl] using hcap N





theorem regionBalls_of_paired_local_steps [FiniteDimensional ℝ E]
    {S C T : Set E} (A : E → ℝ) (d : ℝ → Set E) {a b : ℝ} (hab : a ≤ b)
    (hlocal : ∀ c ∈ Icc a b, ∃ ε : ℝ, 0 < ε ∧
      ∀ u v : ℝ, u ∈ Icc a b → v ∈ Icc a b →
        |u - c| ≤ ε → |v - c| ≤ ε → u ≤ v →
        HasPairedHeightCap S C (d u) A u → HasPairedHeightCap S C (d v) A v)
    (hstart : HasPairedHeightCap S C (d a) A a)
    (hdim : Module.finrank ℝ E = 3)
    (hT : IsFinitePLBallPair ((ℝ × ℝ) × ℝ) T (d b ∪ (S ∩ {x | b ≤ A x})))
    (hTE : IsFinitePLBallPair ((ℝ × ℝ) × ℝ)
      (frontier (C ×ˢ Icc (-1 : ℝ) 1) \ interior T ×ˢ {1})
      ((d b ∪ (S ∩ {x | b ≤ A x})) ×ˢ {(1 : ℝ)}))
    (hd : IsFinitePLBallPair (ℝ × ℝ) (d b) (S ∩ {x | A x = b}))
    (hdplane : d b ⊆ {x | A x = b}) (hdcontact : d b ∩ S = S ∩ {x | A x = b})
    (hTabove : T ⊆ {x | b ≤ A x}) (hTcut : T ∩ {x | A x = b} = d b)
    (hlower : (S ∩ {x | A x < b}).Nonempty)
    (hupper : (S ∩ {x | b < A x}).Nonempty) (hTC : T ⊆ interior C)
    (K : SimplicialComplex ℝ E) (hK : K.faces.Finite)
    (hC : IsCompact C) (hCcv : Convex ℝ C) (hCne : (interior C).Nonempty)
    (hKC : K.space = C) : Set.HasAlexanderRegionBalls S C := by
  have hend := HasPairedHeightCap.continue_of_local_steps A d hab hlocal hstart
  exact hend.regionBalls_of_terminal hdim hT hTE hd hdplane hdcontact hTabove hTcut
    hlower hupper hTC K hK hC hCcv hCne hKC

end PoincareConjecture.M76.ZeroChargeJoint
