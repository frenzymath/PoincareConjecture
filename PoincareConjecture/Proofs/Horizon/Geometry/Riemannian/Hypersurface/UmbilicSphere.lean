import PoincareConjecture.Proofs.Horizon.Geometry.Riemannian.Convexity.Euclidean.SphereMap
import PoincareConjecture.Proofs.Horizon.Geometry.Manifold.MFDeriv.Zero









noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

open Set Filter
open scoped Manifold ContDiff Topology

namespace Poincare.Geometry.Riemannian.Hypersurface

private abbrev E (n : ℕ) := EuclideanSpace ℝ (Fin n)

attribute [local instance] normedAddCommGroupTangentSpaceVectorSpace
  normedSpaceTangentSpaceVectorSpace



theorem surjective_unitMap_of_injective_mfderiv
    {m : ℕ} (hm : 1 ≤ m) {S : Type*} [TopologicalSpace S]
    [ChartedSpace (E m) S] [IsManifold (𝓡 m) ∞ S]
    [CompactSpace S] [Nonempty S]
    (N : S → E (m + 1)) (hN : ContMDiff (𝓡 m) (𝓡 (m + 1)) ∞ N)
    (hunit : ∀ z, ‖N z‖ = 1)
    (hinj : ∀ z, Function.Injective (mfderiv (𝓡 m) (𝓡 (m + 1)) N z)) :
    Function.Surjective (fun z : S =>
      (⟨N z, by simpa only [Metric.mem_sphere, dist_zero_right] using hunit z⟩ :
        Metric.sphere (0 : E (m + 1)) 1)) := by
  let : Fact (Module.finrank ℝ (E (m + 1)) = m + 1) :=
    ⟨finrank_euclideanSpace_fin⟩
  have hrank : 1 < Module.rank ℝ (E (m + 1)) := by
    rw [← Module.finrank_eq_rank, finrank_euclideanSpace_fin]
    exact_mod_cast (show 1 < m + 1 by omega)
  let : ConnectedSpace (Metric.sphere (0 : E (m + 1)) 1) :=
    isConnected_iff_connectedSpace.mp (isConnected_sphere hrank 0 zero_le_one)
  have hmem : ∀ z, N z ∈ Metric.sphere (0 : E (m + 1)) 1 := by
    simpa only [Metric.mem_sphere, dist_zero_right] using hunit
  let F : S → Metric.sphere (0 : E (m + 1)) 1 := Set.codRestrict N _ hmem
  have hF : ContMDiff (𝓡 m) (𝓡 m) ∞ F := hN.codRestrict_sphere hmem
  have hlocal := Convexity.isLocalDiffeomorph_sphere_of_injective_ambient_mfderiv hF hinj
  have hclosed : IsClosed (range F) := (isCompact_range hF.continuous).isClosed
  have hrange : range F = univ :=
    (show IsClopen (range F) from ⟨hclosed, hlocal.isOpen_range⟩).eq_univ
      (range_nonempty F)
  exact range_eq_univ.mp hrange



theorem exists_center_range_sphere_of_unit_derivative
    {m : ℕ} (hm : 1 ≤ m) {S : Type*} [TopologicalSpace S]
    [ChartedSpace (E m) S] [IsManifold (𝓡 m) ∞ S]
    [CompactSpace S] [ConnectedSpace S]
    (f N : S → E (m + 1))
    (hf : ContMDiff (𝓡 m) (𝓡 (m + 1)) ∞ f)
    (hN : ContMDiff (𝓡 m) (𝓡 (m + 1)) ∞ N)
    (himm : ∀ z, Function.Injective (mfderiv (𝓡 m) (𝓡 (m + 1)) f z))
    (hunit : ∀ z, ‖N z‖ = 1)
    (hderiv : ∀ z, mfderiv (𝓡 m) (𝓡 (m + 1)) N z =
      mfderiv (𝓡 m) (𝓡 (m + 1)) f z) :
    ∃ c : E (m + 1), (∀ z, f z - N z = c) ∧ range f = Metric.sphere c 1 := by
  have hconst : IsLocallyConstant (f - N) :=
    PoincareConjecture.isLocallyConstant_of_mfderiv_eq_zero
      ((hf.sub hN).mdifferentiable (by simp)) (fun z => by
        rw [mfderiv_sub (hf.mdifferentiable (by simp) z)
          (hN.mdifferentiable (by simp) z), hderiv z, sub_self])
  obtain ⟨c, hc⟩ := hconst.exists_eq_const
  have hcenter (z : S) : f z - N z = c := congrFun hc z
  have hsurj := surjective_unitMap_of_injective_mfderiv hm N hN hunit
    (fun z => by rw [hderiv z]; exact himm z)
  refine ⟨c, hcenter, Set.Subset.antisymm ?_ ?_⟩
  · rintro _ ⟨z, rfl⟩
    rw [Metric.mem_sphere, dist_eq_norm]
    have hsub : f z - c = N z := by rw [← hcenter z]; abel
    rw [hsub, hunit z]
  · intro y hy
    have hmem : y - c ∈ Metric.sphere (0 : E (m + 1)) 1 := by
      simpa only [Metric.mem_sphere, dist_eq_norm, sub_zero] using hy
    obtain ⟨z, hz⟩ := hsurj ⟨y - c, hmem⟩
    have hz' : N z = y - c := congrArg Subtype.val hz
    refine ⟨z, ?_⟩
    calc
      f z = c + N z := sub_eq_iff_eq_add.mp (hcenter z)
      _ = y := by rw [hz']; abel



theorem exists_homeomorph_sphere_of_injective_unit_derivative
    {m : ℕ} (hm : 1 ≤ m) {S : Type*} [TopologicalSpace S]
    [ChartedSpace (E m) S] [IsManifold (𝓡 m) ∞ S]
    [CompactSpace S] [ConnectedSpace S]
    (f N : S → E (m + 1))
    (hf : ContMDiff (𝓡 m) (𝓡 (m + 1)) ∞ f)
    (hN : ContMDiff (𝓡 m) (𝓡 (m + 1)) ∞ N)
    (himm : ∀ z, Function.Injective (mfderiv (𝓡 m) (𝓡 (m + 1)) f z))
    (hunit : ∀ z, ‖N z‖ = 1)
    (hderiv : ∀ z, mfderiv (𝓡 m) (𝓡 (m + 1)) N z =
      mfderiv (𝓡 m) (𝓡 (m + 1)) f z)
    (hinj : Function.Injective f) :
    ∃ c : E (m + 1), ∃ e : S ≃ₜ Metric.sphere (0 : E (m + 1)) 1,
      ∀ z, (e z : E (m + 1)) = f z - c := by
  let : Fact (Module.finrank ℝ (E (m + 1)) = m + 1) :=
    ⟨finrank_euclideanSpace_fin⟩
  obtain ⟨c, hc, _⟩ := exists_center_range_sphere_of_unit_derivative
    hm f N hf hN himm hunit hderiv
  have hmem : ∀ z, N z ∈ Metric.sphere (0 : E (m + 1)) 1 := by
    simpa only [Metric.mem_sphere, dist_zero_right] using hunit
  let F : S → Metric.sphere (0 : E (m + 1)) 1 := Set.codRestrict N _ hmem
  have hF : ContMDiff (𝓡 m) (𝓡 m) ∞ F := hN.codRestrict_sphere hmem
  have hFiDeriv : ∀ z, Function.Injective
      (mfderiv (𝓡 m) (𝓡 (m + 1)) (fun y => (F y : E (m + 1))) z) := by
    intro z
    change Function.Injective (mfderiv (𝓡 m) (𝓡 (m + 1)) N z)
    rw [hderiv z]
    exact himm z
  have hlocal := Convexity.isLocalDiffeomorph_sphere_of_injective_ambient_mfderiv hF hFiDeriv
  have hFi : Function.Injective F := by
    intro x y hxy
    apply hinj
    have hNxy : N x = N y := congrArg Subtype.val hxy
    have hx : f x = c + N x := sub_eq_iff_eq_add.mp (hc x)
    have hy : f y = c + N y := sub_eq_iff_eq_add.mp (hc y)
    exact hx.trans ((congrArg (fun v => c + v) hNxy).trans hy.symm)
  have hFs : Function.Surjective F :=
    surjective_unitMap_of_injective_mfderiv hm N hN hunit
      (fun z => by rw [hderiv z]; exact himm z)
  let e := (Equiv.ofBijective F ⟨hFi, hFs⟩).toHomeomorphOfContinuousOpen
    hF.continuous hlocal.isOpenMap
  refine ⟨c, e, fun z => ?_⟩
  change N z = f z - c
  rw [← hc z]
  abel

end Poincare.Geometry.Riemannian.Hypersurface
