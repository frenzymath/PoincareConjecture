import PoincareConjecture.Proofs.M14.Sec6_3_StableOpenness











set_option autoImplicit false

open Set
open scoped Manifold ContDiff Bundle

universe u

namespace PoincareConjecture.M14

variable {n : ℕ} {X : Type u} [TopologicalSpace X] {time : X → ℝ}
  {I : SpacetimeInterval} {G : GeneralizedLGeometryTransport n X time I}
  {T τ : ℝ} {x : G.Point}

private theorem tangent_transport_val {p q : G.Point} (h : p = q)
    (v : TangentSpace (spacetimeModel n) p) :
    (show SpacetimeModelVector n from (h ▸ v : TangentSpace (spacetimeModel n) q)) = v := by
  cases h
  rfl





noncomputable def stableSetOfSlicePoint (E : M14ExponentialFamily G T x)
    (hτ : 0 < τ) (q₀ : (G.slices (T - τ)).Point) : M14StableSet G T τ x E := by
  let : Bundle.RiemannianBundle (G.Horizontal : G.Point → Type _) :=
    ⟨G.spacetime.horizontalMetric.toRiemannianMetric⟩
  let C : Set (G.Horizontal x) := {Z | M14StableInitialVector G T τ x E Z}
  let f := exponentialSliceMap E τ hτ.le q₀
  have hC : IsOpen C := isOpen_stableInitialVectors E hτ.le
  have hsurv (Z : G.Horizontal x) (hZ : Z ∈ C) : (Z, Real.sqrt τ) ∈ E.domain := hZ.choose
  have hbij (Z : G.Horizontal x) (hZ : Z ∈ C) :
      Function.Bijective (E.differential Z (Real.sqrt τ) (hsurv Z hZ)) := hZ.choose_spec.1
  have hsm : M14EndpointSliceSmooth G f C :=
    fun Z hZ => (exponentialSliceMap_contMDiffAt E hτ.le q₀ (hsurv Z hZ)).contMDiffWithinAt
  refine {
    tau_pos := hτ
    carrier := C
    carrier_open := hC
    survivor := hsurv
    endpoint_map := fun Z => E.gamma Z (Real.sqrt τ)
    endpoint_map_eq := fun _ _ => rfl
    endpoint_time := fun Z hZ => ?_
    endpoint_slice_map := f
    endpoint_slice_map_val := fun Z hZ => exponentialSliceMap_val E hτ.le q₀ (hsurv Z hZ)
    endpoint_differential := fun Z hZ => E.differential Z (Real.sqrt τ) (hsurv Z hZ)
    endpoint_differential_eq := fun _ _ => rfl
    endpoint_differential_bijective := hbij
    endpoint_continuous := ?_
    endpoint_slice_continuous := hsm.continuousOn
    endpoint_slice_smooth := hsm
    local_inverse := ?_
    endpoint_slice_differential := ?_
    minimizing_path := fun Z hZ => (stableInitialVector_unique_branch E hZ).2
    nonconjugate := hbij
    carrier_exact := fun _ => Iff.rfl
    local_stable_neighborhood := fun _ hZ => stableInitialVector_open_neighborhood E hτ.le hZ }
  · simpa only [Real.sq_sqrt hτ.le] using E.clock Z _ (hsurv Z hZ)
  · exact E.joint_continuous.comp (continuousOn_id.prodMk continuousOn_const)
      (fun Z hZ => hsurv Z hZ)
  · intro Z hZ
    obtain ⟨e, hZe, heC, hef, hinv, _⟩ :=
      exists_exponentialSlice_local_inverse E hτ.le q₀ hC hsurv hZ (hbij Z hZ)
    change EqOn (e : G.Horizontal x → (G.slices (T - τ)).Point) f e.source at hef
    have himage : f '' e.source = e.target :=
      (image_congr (fun W hW => (hef hW).symm)).trans e.image_source_eq_target
    refine ⟨e.source, e.target, e.symm, e.open_source, e.open_target, hZe, ?_, heC,
      himage, e.continuousOn_symm, ?_, fun _ hq => e.map_target hq, hsm.mono heC, hinv, ?_, ?_⟩
    · rw [← hef hZe]
      exact e.map_source hZe
    · intro S hS hSe
      have heq : f '' S = e '' S := image_congr (fun W hW => (hef (hSe hW)).symm)
      rw [heq]
      exact e.isOpen_image_of_subset_source hS hSe
    · intro W hW
      rw [← hef hW]
      exact e.left_inv hW
    · intro q hq
      rw [← hef (e.map_target hq)]
      exact e.right_inv hq
  · intro Z hZ W
    exact (tangent_transport_val (exponentialSliceMap_val E hτ.le q₀ (hsurv Z hZ))
      (((G.slices (T - τ)).tangentEquiv (f Z)) (M14EndpointSliceMfderiv G f Z W)).val).trans
        (exponentialSliceMap_differential_val E hτ.le q₀ (hsurv Z hZ) W)




theorem stableSet_nonempty (E : M14ExponentialFamily G T x) (hτ : 0 < τ)
    (hsurv : ∃ Z, (Z, Real.sqrt τ) ∈ E.domain) : Nonempty (M14StableSet G T τ x E) := by
  obtain ⟨Z, hZ⟩ := hsurv
  let q₀ : (G.slices (T - τ)).Point :=
    ⟨E.gamma Z (Real.sqrt τ), by simpa only [Real.sq_sqrt hτ.le] using E.clock Z _ hZ⟩
  exact ⟨stableSetOfSlicePoint E hτ q₀⟩

end PoincareConjecture.M14
