import PoincareConjecture.Proofs.M64.Sec19_3_Annuli.Plateau.BoundaryTriangularTrace
import PoincareConjecture.Proofs.M64.Sec19_3_Annuli.Plateau.BoundaryTriangularWeak







set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

noncomputable section

open Set Filter MeasureTheory
open scoped Topology ContDiff ENNReal Manifold

namespace PoincareConjecture.M64ObservedWeakAnnulus

open Poincare.Analysis.Sobolev.Weak

variable {n m : ℕ} {M : Type*} [TopologicalSpace M]
  [ChartedSpace (EuclideanSpace ℝ (Fin n)) M]
  {e : M → EuclideanSpace ℝ (Fin m)} {c0 c1 : ℝ → M}

local notation "E" => EuclideanSpace ℝ (Fin m)
local notation "S" => interior m64AnnulusDomain
local notation "mu" => volume.restrict S
local notation "e0" => EuclideanSpace.single (0 : Fin 2) (1 : ℝ)
local notation "e1" => EuclideanSpace.single (1 : Fin 2) (1 : ℝ)




theorem exists_triangularSource
    (A : M64ObservedWeakAnnulus (n := n) e c0 c1)
    (hc0 : Continuous (e ∘ c0)) (hc1 : Continuous (e ∘ c1))
    (T : LoopPlane ≃ₜ LoopPlane) (hT : ContDiff ℝ ∞ T) (hi : ContDiff ℝ ∞ T.symm)
    (hsecond : ∀ p, T p 1 = p 1) (hpos : ∀ p, 0 < fderiv ℝ T p e0 0)
    (hpre : T ⁻¹' S = S)
    (hzero : ∀ s, T (annulusPoint 0 s) = annulusPoint 0 s)
    (hperiod : ∀ s, T (annulusPoint curvePeriod s) = annulusPoint curvePeriod s) :
    ∃ B : M64ObservedWeakAnnulus (n := n) e
        (fun x => c0 (T (annulusPoint x 0) 0)) (fun x => c1 (T (annulusPoint x 1) 0)),
      B.map = A.map ∘ T ∧ ∀ i, ∀ᵐ p ∂mu, B.column i p =
        if i = 0 then fderiv ℝ T p e0 0 • A.column 0 (T p)
        else fderiv ℝ T p e1 0 • A.column 0 (T p) + A.column 1 (T p) := by
  let V := fun (i : Fin 2) (p : LoopPlane) =>
    if i = 0 then fderiv ℝ T p e0 0 • A.column 0 (T p)
    else fderiv ℝ T p e1 0 • A.column 0 (T p) + A.column 1 (T p)
  have hW (i : Fin 2) : MemLp (V i) 2 mu := by
    fin_cases i
    · exact m64TriangularSource_weighted_column_memLp T (hT.of_le (by simp))
        (hi.of_le (by simp)) hsecond hpos hpre (Lp.memLp (A.column 0)) 0
    · exact (m64TriangularSource_weighted_column_memLp T (hT.of_le (by simp))
        (hi.of_le (by simp)) hsecond hpos hpre (Lp.memLp (A.column 0)) 1).add
        (m64TriangularSource_memLp_two T (hT.of_le (by simp)) (hi.of_le (by simp))
          hsecond hpos hpre (Lp.memLp (A.column 1)))
  let column := fun i => (hW i).toLp (V i)
  have hc (i : Fin 2) : (column i : LoopPlane → E) =ᵐ[mu] V i := (hW i).coeFn_toLp
  have hobs : MemLp (e ∘ (A.map ∘ T)) 2 mu :=
    m64TriangularSource_memLp_two T (hT.of_le (by simp)) (hi.of_le (by simp))
      hsecond hpos hpre A.observed_memLp
  have hq := m64Source_quasiMeasurePreserving T (hi.differentiable (by simp)) hpre
  have hint (i : Fin 2) (phi : LoopPlane → ℝ) :
      (∫ p in S, phi p • column i p) = ∫ p in S, phi p • V i p :=
    integral_congr_ae ((hc i).mono fun p hp => congrArg (phi p • ·) hp)
  have hw (i : Fin 2) (b : Fin m) :
      HasWeakPartialDeriv i (fun p => V i p b) (fun p => e (A.map (T p)) b) S := by
    have h := m64TriangularSource_weakPartials T hT hi hsecond hpos hpre
      ((EuclideanSpace.proj (𝕜 := ℝ) b).comp_memLp' A.observed_memLp)
      ((EuclideanSpace.proj (𝕜 := ℝ) b).comp_memLp' (Lp.memLp (A.column 0)))
      ((EuclideanSpace.proj (𝕜 := ℝ) b).comp_memLp' (Lp.memLp (A.column 1)))
      (A.weak_partial 0 b) (A.weak_partial 1 b)
    fin_cases i
    · simpa [V, Function.comp_def] using h.1
    · simpa [V, Function.comp_def] using h.2
  have hseam : ∀ psi : LoopPlane → ℝ, ContDiff ℝ 1 psi →
      (∀ s ∈ Icc (0 : ℝ) 1,
        psi (annulusPoint curvePeriod s) = psi (annulusPoint 0 s)) →
      (∫ p in S, psi p • A.column 0 p) +
        (∫ p in S, fderiv ℝ psi p e0 • e (A.map p)) =
      (∫ s in Icc (0 : ℝ) 1, psi (annulusPoint curvePeriod s)) • (0 : E) := by
    intro psi hpsi hperiod
    simpa only [smul_zero] using A.seam psi hpsi hperiod
  let B : M64ObservedWeakAnnulus (n := n) e
      (fun x => c0 (T (annulusPoint x 0) 0)) (fun x => c1 (T (annulusPoint x 1) 0)) := {
    map := A.map ∘ T
    observed_memLp := hobs
    column := column
    tangent := fun i => by
      filter_upwards [hc i, hq.ae (A.tangent 0), hq.ae (A.tangent 1)] with p hp htan0 htan1
      obtain ⟨v0, hv0⟩ := htan0
      obtain ⟨v1, hv1⟩ := htan1
      let L := mfderiv (𝓡 n) (𝓡 m) e (A.map (T p))
      fin_cases i
      · refine ⟨fderiv ℝ T p e0 0 • v0, ?_⟩
        change L (fderiv ℝ T p e0 0 • v0) = column 0 p
        calc
          _ = fderiv ℝ T p e0 0 • A.column 0 (T p) := by rw [map_smul, hv0]
          _ = _ := hp.symm
      · refine ⟨fderiv ℝ T p e1 0 • v0 + v1, ?_⟩
        change L (fderiv ℝ T p e1 0 • v0 + v1) = column 1 p
        calc
          _ = fderiv ℝ T p e1 0 • A.column 0 (T p) + A.column 1 (T p) := by
            rw [map_add, map_smul, hv0, hv1]
          _ = _ := hp.symm
    weak_partial := fun i b =>
      m64WeakPartialDeriv_ae_congr EventuallyEq.rfl
        ((hc i).symm.mono fun p hp => congrArg (fun v : E => v b) hp) (hw i b)
    boundary := fun phi hp => by
      rw [hint]
      simpa only [V, show (1 : Fin 2) ≠ 0 from by decide, ite_false,
        Function.comp_apply] using
        m64TriangularSource_preserves_boundary T hT hi hsecond hpos hpre hzero hperiod
          A.observed_memLp (Lp.memLp (A.column 0)) (Lp.memLp (A.column 1)) hc0 hc1 0
          A.boundary hseam phi hp
    seam := fun phi hp hs => by
      rw [hint]
      simpa only [V, ite_true, Function.comp_apply, smul_zero] using
        m64TriangularSource_preserves_seam T hT hi hsecond hpos hpre hzero hperiod
          (e ∘ A.map) (A.column 0) 0 hseam phi hp hs }
  exact ⟨B, rfl, hc⟩

end PoincareConjecture.M64ObservedWeakAnnulus
