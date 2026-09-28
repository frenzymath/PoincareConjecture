import PoincareConjecture.Proofs.Horizon.Geometry.RicciFlow.ConjugateHeat.WeakPairing
import PoincareConjecture.Proofs.Horizon.Geometry.RicciFlow.ConjugateHeat.Coordinates.Laplacian
import PoincareConjecture.Proofs.Horizon.Geometry.Riemannian.ScalarOperators.Divergence.Regularity

noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

open Set Filter
open scoped Manifold ContDiff Topology
open Poincare.Analysis.Parabolic.WeakRegularity
open Poincare.Analysis.Elliptic.Iteration
open Poincare.Analysis.Elliptic.InteriorEstimates

namespace PoincareConjecture.RicciFlow.ConjugateHeat

variable {n : ℕ} {M : Type*} [TopologicalSpace M]
  [ChartedSpace (EuclideanSpace ℝ (Fin n)) M] [IsManifold (𝓡 n) ∞ M]
  {J : Set ℝ}

theorem testOperator_eq_zero_of_notMem_tsupport (F : RicciFlow n M J)
    {φ : M × ℝ → ℝ} {z : M × ℝ} (hz : z ∉ tsupport φ) :
    testOperator F φ z = 0 := by
  have heq := notMem_tsupport_iff_eventuallyEq.mp hz
  have ht : (fun τ => φ (z.1, τ)) =ᶠ[𝓝 z.2] (fun _ => (0 : ℝ)) :=
    heq.comp_tendsto ((continuous_const.prodMk continuous_id).tendsto z.2)
  have hx : (fun x => φ (x, z.2)) =ᶠ[𝓝 z.1] (fun _ => (0 : ℝ)) :=
    heq.comp_tendsto ((continuous_id.prodMk continuous_const).tendsto z.1)
  rw [testOperator, ht.deriv_eq,
    (F.connection (-z.2)).laplacian_eq_zero_of_notMem_tsupport
      (notMem_tsupport_iff_eventuallyEq.mpr hx)]
  simp

theorem tsupport_testOperator_subset (F : RicciFlow n M J) (φ : M × ℝ → ℝ) :
    tsupport (testOperator F φ) ⊆ tsupport φ := by
  apply closure_minimal _ (isClosed_tsupport _)
  intro z hz
  by_contra hφ
  exact hz (testOperator_eq_zero_of_notMem_tsupport F hφ)

theorem hasCompactSupport_testOperator (F : RicciFlow n M J)
    {φ : M × ℝ → ℝ} (hφ : HasCompactSupport φ) :
    HasCompactSupport (testOperator F φ) :=
  hφ.of_isClosed_subset (isClosed_tsupport _) (tsupport_testOperator_subset F φ)

private theorem partialDeriv_partialDeriv_slice_of_contDiffOn
    {f : Spacetime n → ℝ} {V : Set (Spacetime n)} (hV : IsOpen V)
    (hf : ContDiffOn ℝ ∞ f V) {z : Spacetime n} (hz : z ∈ V) (i j : Fin n) :
    partialDeriv i (partialDeriv j (fun y => f (y, z.2))) z.1 =
      Canonical.spatialDeriv i (Canonical.spatialDeriv j f) z := by
  have hd : ContDiffOn ℝ ∞ (Canonical.spatialDeriv j f) V :=
    (hf.fderiv_of_isOpen hV (by simp)).clm_apply contDiffOn_const
  have heq : partialDeriv j (fun y => f (y, z.2)) =ᶠ[𝓝 z.1]
      (fun y => Canonical.spatialDeriv j f (y, z.2)) := by
    filter_upwards [((continuous_id.prodMk continuous_const).tendsto z.1)
      (hV.mem_nhds hz)] with y hy
    exact BackwardCoordinates.partialDeriv_spatialSlice
      ((hf.contDiffAt (hV.mem_nhds hy)).differentiableAt (by simp)) j
  change fderiv ℝ (partialDeriv j (fun y => f (y, z.2))) z.1
      (EuclideanSpace.single i 1) = _
  rw [heq.fderiv_eq]
  exact BackwardCoordinates.partialDeriv_spatialSlice
    ((hd.contDiffAt (hV.mem_nhds hz)).differentiableAt (by simp)) i

private theorem timeDeriv_eq_deriv_slice {f : Spacetime n → ℝ} {z : Spacetime n}
    (hf : DifferentiableAt ℝ f z) :
    Canonical.timeDeriv f z = deriv (fun τ => f (z.1, τ)) z.2 := by
  have hd := hf.hasFDerivAt.comp_hasDerivAt z.2
    ((hasDerivAt_const z.2 z.1).prodMk (hasDerivAt_id z.2))
  exact hd.deriv.symm

private theorem contDiffOn_testOperator_coordinates
    (F : RicciFlow n M J)
    (e : OpenPartialHomeomorph (EuclideanSpace ℝ (Fin n)) M)
    (he : ContMDiffOn (𝓡 n) (𝓡 n) ∞ e e.source)
    (hei : ContMDiffOn (𝓡 n) (𝓡 n) ∞ e.symm e.target)
    {φ : M × ℝ → ℝ}
    (hφ : ContMDiff ((𝓡 n).prod 𝓘(ℝ, ℝ)) 𝓘(ℝ, ℝ) ∞ φ) :
    ContDiffOn ℝ ∞ (fun z : Spacetime n => testOperator F φ (e z.1, z.2))
      (BackwardCoordinates.domain J e) := by
  let ψ : Spacetime n → ℝ := fun z => φ (e z.1, z.2)
  let V := BackwardCoordinates.domain J e
  have hV : IsOpen V := BackwardCoordinates.isOpen_domain e
  have hψ : ContDiffOn ℝ ∞ ψ V := by
    intro z hz
    have hmap : ContMDiffAt ((𝓡 n).prod 𝓘(ℝ, ℝ))
        ((𝓡 n).prod 𝓘(ℝ, ℝ)) ∞
        (fun y : Spacetime n => (e y.1, y.2)) z :=
      ((he.contMDiffAt (e.open_source.mem_nhds hz.1)).comp z
        contMDiffAt_fst).prodMk contMDiffAt_snd
    have h := (hφ (e z.1, z.2)).comp z hmap
    simp +instances only [← modelWithCornersSelf_prod, chartedSpaceSelf_prod] at h
    exact h.contDiffAt.contDiffWithinAt
  have hd (i : Fin n) : ContDiffOn ℝ ∞ (Canonical.spatialDeriv i ψ) V :=
    (hψ.fderiv_of_isOpen hV (by simp)).clm_apply contDiffOn_const
  have hdd (i j : Fin n) :
      ContDiffOn ℝ ∞ (Canonical.spatialDeriv i (Canonical.spatialDeriv j ψ)) V :=
    ((hd j).fderiv_of_isOpen hV (by simp)).clm_apply contDiffOn_const
  have htime : ContDiffOn ℝ ∞ (Canonical.timeDeriv ψ) V :=
    (hψ.fderiv_of_isOpen hV (by simp)).clm_apply contDiffOn_const
  have hop : ContDiffOn ℝ ∞ (fun z => Canonical.timeDeriv ψ z +
      ((∑ i, ∑ j, BackwardCoordinates.principal F e i j z *
        Canonical.spatialDeriv i (Canonical.spatialDeriv j ψ) z) +
      ∑ i, BackwardCoordinates.drift F e i z * Canonical.spatialDeriv i ψ z)) V :=
    htime.add ((ContDiffOn.sum (fun i _ => ContDiffOn.sum (fun j _ =>
      (BackwardCoordinates.contDiffOn_principal F e he hei i j).mul (hdd i j)))).add
      (ContDiffOn.sum (fun i _ =>
        (BackwardCoordinates.contDiffOn_drift F e he hei i).mul (hd i))))
  apply hop.congr
  intro z hz
  symm
  have hs : ContMDiff (𝓡 n) 𝓘(ℝ, ℝ) ∞ (fun x => φ (x, z.2)) :=
    hφ.comp (contMDiff_id.prodMk contMDiff_const)
  have hL := LeviCivitaData.Dirichlet.secondOrderOperator_coordinate_eq_laplacian
    (F.connection (-z.2)) e he hei isOpen_univ hs.contMDiffOn hz.1 (mem_univ _)
  rw [timeDeriv_eq_deriv_slice ((hψ.contDiffAt (hV.mem_nhds hz)).differentiableAt
    (by simp))]
  change deriv (fun τ => φ (e z.1, τ)) z.2 + _ = testOperator F φ (e z.1, z.2)
  rw [testOperator, ← hL]
  congr 1
  unfold secondOrderOperator
  congr 1
  · apply Finset.sum_congr rfl
    intro i _
    apply Finset.sum_congr rfl
    intro j _
    rw [← BackwardCoordinates.principal_eq_coordinatePrincipal F e he hei hz.1 i j]
    congr 1
    exact (partialDeriv_partialDeriv_slice_of_contDiffOn hV hψ hz i j).symm
  · apply Finset.sum_congr rfl
    intro i _
    rw [← BackwardCoordinates.drift_eq_coordinateDrift F e he hei hz i]
    congr 1
    exact (BackwardCoordinates.partialDeriv_spatialSlice
      ((hψ.contDiffAt (hV.mem_nhds hz)).differentiableAt (by simp)) i).symm

theorem contMDiffOn_testOperator (F : RicciFlow n M J)
    {φ : M × ℝ → ℝ}
    (hφ : ContMDiff ((𝓡 n).prod 𝓘(ℝ, ℝ)) 𝓘(ℝ, ℝ) ∞ φ) :
    ContMDiffOn ((𝓡 n).prod 𝓘(ℝ, ℝ)) 𝓘(ℝ, ℝ) ∞ (testOperator F φ)
      (univ ×ˢ ((fun τ : ℝ => -τ) ⁻¹' interior J)) := by
  intro z hz
  let e := (chartAt (EuclideanSpace ℝ (Fin n)) z.1).symm
  have he : ContMDiffOn (𝓡 n) (𝓡 n) ∞ e e.source := contMDiffOn_chart_symm
  have hei : ContMDiffOn (𝓡 n) (𝓡 n) ∞ e.symm e.target := contMDiffOn_chart
  have hp : z.1 ∈ e.target := mem_chart_source _ z.1
  have hx : (e.symm z.1, z.2) ∈ BackwardCoordinates.domain J e :=
    ⟨e.map_target hp, hz.2⟩
  have hcoord := (contDiffOn_testOperator_coordinates F e he hei hφ).contDiffAt
    ((BackwardCoordinates.isOpen_domain e).mem_nhds hx)
  have hmap : ContMDiffAt ((𝓡 n).prod 𝓘(ℝ, ℝ))
      𝓘(ℝ, Spacetime n) ∞ (fun y : M × ℝ => (e.symm y.1, y.2)) z :=
    ((hei.contMDiffAt (e.open_target.mem_nhds hp)).comp z
      contMDiffAt_fst).prodMk_space contMDiffAt_snd
  apply ((hcoord.contMDiffAt.comp z hmap).congr_of_eventuallyEq ?_).contMDiffWithinAt
  filter_upwards [(continuous_fst.tendsto z) (e.open_target.mem_nhds hp)] with y hy
  change testOperator F φ y = testOperator F φ (e (e.symm y.1), y.2)
  rw [e.right_inv hy]

theorem contMDiff_testOperator_of_tsupport_subset (F : RicciFlow n M J)
    {φ : M × ℝ → ℝ}
    (hφ : ContMDiff ((𝓡 n).prod 𝓘(ℝ, ℝ)) 𝓘(ℝ, ℝ) ∞ φ)
    (hs : tsupport φ ⊆ univ ×ˢ ((fun τ : ℝ => -τ) ⁻¹' interior J)) :
    ContMDiff ((𝓡 n).prod 𝓘(ℝ, ℝ)) 𝓘(ℝ, ℝ) ∞ (testOperator F φ) := by
  intro z
  by_cases hz : z ∈ univ ×ˢ ((fun τ : ℝ => -τ) ⁻¹' interior J)
  · exact (contMDiffOn_testOperator F hφ).contMDiffAt
      ((isOpen_univ.prod (isOpen_interior.preimage continuous_neg)).mem_nhds hz)
  · have hzs : z ∉ tsupport (testOperator F φ) :=
      fun h => hz (hs (tsupport_testOperator_subset F φ h))
    exact contMDiffAt_const.congr_of_eventuallyEq
      (notMem_tsupport_iff_eventuallyEq.mp hzs)

end PoincareConjecture.RicciFlow.ConjugateHeat
