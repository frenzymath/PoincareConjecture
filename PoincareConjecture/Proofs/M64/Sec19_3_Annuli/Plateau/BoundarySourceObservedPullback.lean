import PoincareConjecture.Proofs.M64.Sec19_3_Annuli.Plateau.BoundarySourceHorizontalTrace

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

noncomputable section

open Set Filter MeasureTheory
open scoped Topology ContDiff ENNReal Manifold

namespace PoincareConjecture

local notation "S" => interior m64AnnulusDomain
local notation "mu" => volume.restrict S

theorem m64HorizontalSource_column_memLp_two
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] {V : LoopPlane → E}
    {tau : ℝ ≃ₜ ℝ} (ht : ContDiff ℝ 1 tau) (hi : ContDiff ℝ 1 tau.symm)
    (hpos : ∀ x, 0 < deriv tau x) (hmono : StrictMono tau)
    (h0 : tau 0 = 0) (hP : tau curvePeriod = curvePeriod) (hV : MemLp V 2 mu)
    (i : Fin 2) :
    MemLp (fun p => (if i = 0 then deriv tau (p 0) else 1) •
      V (m64HorizontalSource tau p)) 2 mu := by
  let a := fun p : LoopPlane => if i = 0 then deriv tau (p 0) else 1
  have ha : Continuous a := by
    by_cases hi : i = 0
    · simp only [a, hi, ite_true]
      exact (ht.continuous_deriv (by simp)).comp
        (EuclideanSpace.proj (0 : Fin 2) : LoopPlane →L[ℝ] ℝ).continuous
    · simpa only [a, hi, ite_false] using
        (continuous_const : Continuous (fun _ : LoopPlane => (1 : ℝ)))
  obtain ⟨C, hC⟩ := m64AnnulusDomain_isCompact.exists_bound_of_continuousOn ha.continuousOn
  have htop : MemLp a ∞ mu := memLp_top_of_bound ha.aestronglyMeasurable C (by
    filter_upwards [ae_restrict_mem isOpen_interior.measurableSet] with p hp
    exact hC p (interior_subset hp))
  exact (m64HorizontalSource_memLp_two ht hi hpos hmono h0 hP hV).smul htop

namespace M64ObservedWeakAnnulus

variable {n m : ℕ} {M : Type*} [TopologicalSpace M]
  [ChartedSpace (EuclideanSpace ℝ (Fin n)) M]
  {e : M → EuclideanSpace ℝ (Fin m)} {c0 c1 : ℝ → M}

local notation "E" => EuclideanSpace ℝ (Fin m)

theorem exists_horizontalSource
    (A : M64ObservedWeakAnnulus (n := n) e c0 c1)
    {tau : ℝ ≃ₜ ℝ} (ht : ContDiff ℝ ∞ tau) (hi : ContDiff ℝ ∞ tau.symm)
    (hpos : ∀ x, 0 < deriv tau x) (hmono : StrictMono tau)
    (h0 : tau 0 = 0) (hP : tau curvePeriod = curvePeriod) :
    ∃ B : M64ObservedWeakAnnulus (n := n) e (c0 ∘ tau) (c1 ∘ tau),
      B.map = A.map ∘ m64HorizontalSource tau ∧
      ∀ i, ∀ᵐ p ∂mu, B.column i p =
        (if i = 0 then deriv tau (p 0) else 1) • A.column i (m64HorizontalSource tau p) := by
  let T := m64HorizontalSource tau
  let V := fun (i : Fin 2) (p : LoopPlane) =>
    (if i = 0 then deriv tau (p 0) else 1) • A.column i (T p)
  have hV (i : Fin 2) : MemLp (V i) 2 mu :=
    m64HorizontalSource_column_memLp_two (ht.of_le (by simp)) (hi.of_le (by simp))
      hpos hmono h0 hP (Lp.memLp (A.column i)) i
  let column := fun i => (hV i).toLp (V i)
  have hc (i : Fin 2) : (column i : LoopPlane → E) =ᵐ[mu] V i := (hV i).coeFn_toLp
  have hobs : MemLp (e ∘ (A.map ∘ T)) 2 mu :=
    m64HorizontalSource_memLp_two (ht.of_le (by simp)) (hi.of_le (by simp))
      hpos hmono h0 hP A.observed_memLp
  have hq := m64HorizontalSource_quasiMeasurePreserving (hi.of_le (by simp)) hmono h0 hP
  have hint (i : Fin 2) (phi : LoopPlane → ℝ) :
      (∫ p in S, phi p • column i p) = ∫ p in S, phi p • V i p :=
    integral_congr_ae ((hc i).mono fun p hp => congrArg (phi p • ·) hp)
  let B : M64ObservedWeakAnnulus (n := n) e (c0 ∘ tau) (c1 ∘ tau) := {
    map := A.map ∘ T
    observed_memLp := hobs
    column := column
    tangent := fun i => by
      filter_upwards [hc i, hq.ae (A.tangent i)] with p hp htan
      obtain ⟨v, hv⟩ := htan
      refine ⟨(if i = 0 then deriv tau (p 0) else 1) • v, ?_⟩
      exact ((mfderiv (𝓡 n) (𝓡 m) e (A.map (T p))).map_smul
        (if i = 0 then deriv tau (p 0) else 1) v).trans
          ((congrArg (fun w : E => (if i = 0 then deriv tau (p 0) else 1) • w) hv).trans hp.symm)
    weak_partial := fun i b => by
      apply m64WeakPartialDeriv_ae_congr (EventuallyEq.rfl)
        ((hc i).symm.mono fun p hp => congrArg (fun v : E => v b) hp)
      simpa only [V, PiLp.smul_apply, smul_eq_mul, Function.comp_def, T] using
        m64HorizontalSource_weakPartial ht hi hpos hmono h0 hP (A.weak_partial i b)
    boundary := fun phi hp => by
      rw [hint]
      simpa only [V, show (1 : Fin 2) ≠ 0 from by decide, ite_false, one_smul,
        Function.comp_apply] using
        m64HorizontalSource_preserves_boundary ht hi hpos hmono h0 hP
          (e ∘ A.map) (A.column 1) (e ∘ c0) (e ∘ c1) A.boundary phi hp
    seam := fun phi hp hs => by
      rw [hint]
      have hseam : ∀ psi : LoopPlane → ℝ, ContDiff ℝ 1 psi →
          (∀ s ∈ Icc (0 : ℝ) 1,
            psi (annulusPoint curvePeriod s) = psi (annulusPoint 0 s)) →
          (∫ p in S, psi p • A.column 0 p) +
            (∫ p in S, fderiv ℝ psi p (EuclideanSpace.single (0 : Fin 2) 1) • e (A.map p)) =
          (∫ s in Icc (0 : ℝ) 1, psi (annulusPoint curvePeriod s)) • (0 : E) := by
        intro psi hpsi hperiod
        simpa only [smul_zero] using A.seam psi hpsi hperiod
      simpa only [V, ite_true, Function.comp_apply, smul_zero] using
        m64HorizontalSource_preserves_seam ht hi hpos hmono h0 hP
          (e ∘ A.map) (A.column 0) 0 hseam phi hp hs }
  exact ⟨B, rfl, hc⟩

end M64ObservedWeakAnnulus
end PoincareConjecture
