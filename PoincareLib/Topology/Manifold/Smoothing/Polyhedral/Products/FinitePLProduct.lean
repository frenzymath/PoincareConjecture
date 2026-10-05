import PoincareLib.Topology.Manifold.Smoothing.Polyhedral.Affine.FinitePiecewiseAffine
import PoincareLib.Topology.Manifold.Smoothing.Polyhedral.Simplicial.CommonSimplicialRefinement

/-!
# Finite products of PL coordinate maps

A finite family of face-affine maps on one finite carrier admits
one common source subdivision and a face-affine product map. See
Hudson 1969, pp. 12--19, Hamilton 1976, p. 69 and M76 derivation
258. The starting carrier is retained so empty index families
remain meaningful.
-/

set_option autoImplicit false

open Set

namespace Geometry

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [FiniteDimensional ℝ E]

/-- A finite dependent family of finite PL maps on one carrier
has a finite PL product after a common simplicial refinement.
The theorem is stated with an explicit starting complex so it
also covers an empty family. See Hudson pp. 12--19 and M76
derivation 258. -/
theorem FinitePiecewiseAffineOn.pi_on_complex
    {ι : Type*} [Fintype ι] {F : ι → Type*}
    [∀ i, NormedAddCommGroup (F i)] [∀ i, NormedSpace ℝ (F i)]
    [∀ i, FiniteDimensional ℝ (F i)]
    (K : SimplicialComplex ℝ E) (hK : K.faces.Finite)
    {f : ∀ i, E → F i}
    (hf : ∀ i, FinitePiecewiseAffineOn (f i) K.space) :
    FinitePiecewiseAffineOn (fun x i => f i x) K.space := by
  classical
  have hstep : ∀ t : Finset ι, ∃ L : SimplicialComplex ℝ E,
      L.faces.Finite ∧ L.space = K.space ∧
      ∀ i ∈ t, L.AffineOnFaces (f i) := by
    intro t
    induction t using Finset.induction_on with
    | empty =>
        exact ⟨K, hK, rfl, by simp⟩
    | @insert i t hi ih =>
        obtain ⟨L, hL, hLK, hprev⟩ := ih
        obtain ⟨Ki, hKi, hKiK, hfi⟩ := hf i
        obtain ⟨R, hR, hRL, hRi⟩ :=
          SimplicialComplex.exists_common_finite_subdivision L Ki hL hKi
            (hLK.trans hKiK.symm)
        refine ⟨R, hR, hRL.space_eq.trans hLK, ?_⟩
        intro j hj
        rcases Finset.mem_insert.mp hj with rfl | hj
        · exact hRi.affineOnFaces hfi
        · exact hRL.affineOnFaces (hprev j hj)
  obtain ⟨L, hL, hLK, hall⟩ := hstep Finset.univ
  refine ⟨L, hL, hLK, ?_⟩
  intro s hs
  choose a ha using fun i => hall i (Finset.mem_univ i) s hs
  let b : E →ᴬ[ℝ] (∀ i, F i) :=
    ⟨AffineMap.pi (fun i => (a i).toAffineMap), continuous_pi (fun i => (a i).continuous)⟩
  refine ⟨b, ?_⟩
  intro x hx
  funext i
  exact ha i hx

end Geometry
