import PoincareConjecture.Proofs.M76.Horizon.PrimeReduction.Cutting.PuncturedSphereModel
import PoincareConjecture.Proofs.M76.Wall.OriginalFinitePLSphereImage
import PoincareConjecture.Proofs.M76.Rigidity.Mathlib.CubePrismBoundary

set_option autoImplicit false
open Set Metric Geometry

namespace PoincareConjecture.M76

local notation "V3" => (Fin 3 → ℝ)
local notation "V4" => (Fin 4 → ℝ)
local notation "Sphere" => Geometry.CubicalThreeSphere.sphere
local notation "CubeSphere" => sphere (0 : V3) 1

theorem exists_original_punctured_model_boundary_spheres
    {X E ι κ : Type*} [TopologicalSpace X] [T2Space X]
    [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
    {e : ι → OpenPartialHomeomorph X V3} {R : Set X} {M : Set E}
    (hR : IsClosed R) (K : SimplicialComplex ℝ E) (g : E → X)
    (hg : PolyhedralPLInCharts e g K.space) (hgi : InjOn g K.space)
    (hMK : M ⊆ K.space) (G : R ≃ₜ M) (hginv : ∀ x : R, g (G x) = (x : X))
    (A r : κ → Set V4) (hA : ∀ i, IsFinitePLBallPair V3 (A i) (r i))
    (hAS : ∀ i, A i ⊆ Sphere)
    (hAdis : Pairwise fun i j => Disjoint (A i) (A j))
    (C : M ≃ₜ (Sphere \ ⋃ i, A i \ r i : Set V4)) (hC : C.IsFinitePL)
    (hmark : ∀ x : R, (x : X) ∈ frontier R ↔ (C (G x) : V4) ∈ ⋃ i, r i) :
    ∃ (S : κ → Set X) (sS : ∀ i, ChartwisePLSphere e (S i)),
      (∀ i, S i = g '' ((Subtype.val : M → E) ''
        ((fun y : M => (C y : V4)) ⁻¹' r i))) ∧
      (∀ i, S i ⊆ R) ∧
      Pairwise (fun i j => Disjoint (S i) (S j)) ∧
      frontier R = ⋃ i, S i ∧
      (∀ i (x : R), (x : X) ∈ S i ↔ (C (G x) : V4) ∈ r i) ∧
      ∀ i, (fun x : R => (C (G x) : V4)) ''
        ((Subtype.val : R → X) ⁻¹' S i) = r i := by
  classical
  let Q := Sphere \ ⋃ i, A i \ r i
  let T : κ → Set E := fun i => (Subtype.val : M → E) ''
    ((fun y : M => (C y : V4)) ⁻¹' r i)
  let S : κ → Set X := fun i => g '' T i
  have hTM (i : κ) : T i ⊆ M := by
    rintro _ ⟨x, _, rfl⟩
    exact x.property
  have hTmark (i : κ) (x : M) : (x : E) ∈ T i ↔ (C x : V4) ∈ r i := by
    constructor
    · rintro ⟨y, hy, hyx⟩
      exact (Subtype.ext hyx : y = x) ▸ hy
    · exact fun hx => ⟨x, hx, rfl⟩
  have hrQ (i : κ) : r i ⊆ Q := by
    intro x hx
    refine ⟨hAS i ((hA i).1 hx), ?_⟩
    intro hh
    obtain ⟨j, hja, hjr⟩ := mem_iUnion.mp hh
    by_cases hji : j = i
    · exact hjr (hji.symm ▸ hx)
    · exact disjoint_left.mp (hAdis hji) hja ((hA i).1 hx)
  have hspheres (i : κ) : Nonempty (ChartwisePLSphere e (S i)) := by
    obtain ⟨D, hD, hDb⟩ := (hA i).exists_cube_chart (ContinuousLinearEquiv.refl ℝ V3)
    have hDb' (x : A i) : (x : V4) ∈ r i ↔ (D x : V3) ∈ CubeSphere := by
      simpa only [frontier_closedBall _ one_ne_zero] using hDb x
    let d := D.restrictSubsets (hA i).1 sphere_subset_closedBall hDb'
    obtain ⟨L, hL, hLS⟩ := exists_finite_unitCubeSphere (ι := Fin 3)
    have hd : d.IsFinitePL := hD.restrictSubsets_of_target
      (hA i).1 sphere_subset_closedBall hDb' L hL hLS
    have hdcopy := hd
    obtain ⟨_, ⟨J, hJ, hJr, _⟩, _⟩ := hdcopy
    let H := C.restrictSubsets (hTM i) (hrQ i) (hTmark i)
    have hH : H.IsFinitePL := hC.restrictSubsets_of_target
      (hTM i) (hrQ i) (hTmark i) J hJ hJr
    exact exists_chartwisePLSphere_image K hg hgi ((hTM i).trans hMK)
      (H.trans d) (hH.trans hd)
  let sS : ∀ i, ChartwisePLSphere e (S i) := fun i => Classical.choice (hspheres i)
  have hSsub (i : κ) : S i ⊆ R := by
    rintro _ ⟨y, hy, rfl⟩
    let x := G.symm ⟨y, hTM i hy⟩
    have hval : g y = (x : X) := by
      simpa only [x,G.apply_symm_apply] using hginv x
    exact hval.symm ▸ x.property
  have hphysical (i : κ) (x : R) : (x : X) ∈ S i ↔ (C (G x) : V4) ∈ r i := by
    constructor
    · rintro ⟨y, hy, hyx⟩
      have heq : y = (G x : E) := hgi (hMK (hTM i hy)) (hMK (G x).property)
        (hyx.trans (hginv x).symm)
      exact (hTmark i (G x)).mp (heq ▸ hy)
    · intro hx
      exact ⟨G x, (hTmark i (G x)).mpr hx, hginv x⟩
  have hSdis : Pairwise fun i j => Disjoint (S i) (S j) := by
    intro i j hij
    apply disjoint_left.mpr
    intro x hxi hxj
    let y : R := ⟨x, hSsub i hxi⟩
    exact disjoint_left.mp (hAdis hij)
      ((hA i).1 ((hphysical i y).mp hxi)) ((hA j).1 ((hphysical j y).mp hxj))
  have hfront : frontier R = ⋃ i, S i := by
    apply Subset.antisymm
    · intro x hx
      let y : R := ⟨x, hR.frontier_subset hx⟩
      obtain ⟨i, hi⟩ := mem_iUnion.mp ((hmark y).mp hx)
      exact mem_iUnion.mpr ⟨i, (hphysical i y).mpr hi⟩
    · intro x hx
      obtain ⟨i, hi⟩ := mem_iUnion.mp hx
      let y : R := ⟨x, hSsub i hi⟩
      exact (hmark y).mpr (mem_iUnion.mpr ⟨i, (hphysical i y).mp hi⟩)
  refine ⟨S, sS, fun _ => rfl, hSsub, hSdis, hfront, hphysical, ?_⟩
  intro i
  apply Subset.antisymm
  · rintro _ ⟨x, hx, rfl⟩
    exact (hphysical i x).mp hx
  · intro z hz
    let x := G.symm (C.symm ⟨z, hrQ i hz⟩)
    have hvalue : (C (G x) : V4) = z := by
      dsimp only [x]
      rw [G.apply_symm_apply,C.apply_symm_apply]
    exact ⟨x, (hphysical i x).mpr (hvalue.symm ▸ hz), hvalue⟩

theorem HasPuncturedSphereModel.exists_boundary_spheres
    {X E ι : Type*} [TopologicalSpace X] [T2Space X]
    [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
    {e : ι → OpenPartialHomeomorph X V3} {R : Set X} {f : X → E}
    (hmodel : HasPuncturedSphereModel e f R) (hR : IsClosed R)
    (K : SimplicialComplex ℝ E) (g : E → X)
    (hg : PolyhedralPLInCharts e g K.space) (hgi : InjOn g K.space)
    (hreal : ∀ x ∈ R, f x ∈ K.space ∧ g (f x) = x) :
    ∃ (n : ℕ) (S : Fin n → Set X) (sS : ∀ i, ChartwisePLSphere e (S i)),
      (∀ i, S i ⊆ R) ∧ Pairwise (fun i j => Disjoint (S i) (S j)) ∧
      frontier R = ⋃ i, S i := by
  obtain ⟨_, n, A, r, M, G, C, hA, hAdis, hG, hC, hmark⟩ := hmodel
  have hMK : M ⊆ K.space := by
    intro y hy
    let x := G.symm ⟨y, hy⟩
    have hval : f x = y := (hG x).symm.trans
      (congrArg Subtype.val (G.apply_symm_apply _))
    exact hval ▸ (hreal x x.property).1
  have hginv (x : R) : g (G x) = (x : X) := by
    rw [hG x]
    exact (hreal x x.property).2
  obtain ⟨S, sS, _, hsub, hdis, hfront, _, _⟩ :=
    exists_original_punctured_model_boundary_spheres hR K g hg hgi hMK G hginv
      A r (fun i => (hA i).1) (fun i => (hA i).2.1) hAdis C hC hmark
  exact ⟨n, S, sS, hsub, hdis, hfront⟩

end PoincareConjecture.M76
