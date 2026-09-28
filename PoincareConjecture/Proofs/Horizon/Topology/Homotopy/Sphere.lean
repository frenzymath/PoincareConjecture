import PoincareConjecture.Proofs.Horizon.Topology.Homotopy.OpenCover
import Mathlib.Analysis.Normed.Module.Connected
import Mathlib.Geometry.Manifold.Instances.Sphere












noncomputable section
namespace Poincare.Topology

open Metric Set





theorem sphereComplementHomeomorphEuclidean {n : ℕ}
    (x : Metric.sphere (0 : EuclideanSpace ℝ (Fin (n + 1))) 1) :
    Nonempty ((({x}ᶜ : Set
      (Metric.sphere (0 : EuclideanSpace ℝ (Fin (n + 1))) 1))) ≃ₜ
      EuclideanSpace ℝ (Fin n)) := by
  letI : Fact (Module.finrank ℝ (EuclideanSpace ℝ (Fin (n + 1))) = n + 1) :=
    Fact.mk (finrank_euclideanSpace_fin (𝕜 := ℝ) (n := n + 1))
  refine ⟨(Homeomorph.setCongr (stereographic'_source (n := n) x).symm).trans
    (((stereographic' n x).toHomeomorphSourceTarget.trans
      (Homeomorph.setCongr (stereographic'_target (n := n) x))).trans
      (Homeomorph.Set.univ _))⟩



theorem sphereComplementTwoPointsHomeomorphPuncturedEuclidean {n : ℕ}
    (v : Metric.sphere (0 : EuclideanSpace ℝ (Fin (n + 2))) 1) :
    Nonempty ((({v, -v}ᶜ : Set
      (Metric.sphere (0 : EuclideanSpace ℝ (Fin (n + 2))) 1))) ≃ₜ
      ({0}ᶜ : Set (EuclideanSpace ℝ (Fin (n + 1))))) := by
  letI : Fact
      (Module.finrank ℝ (EuclideanSpace ℝ (Fin (n + 2))) = (n + 1) + 1) :=
    Fact.mk (by rw [finrank_euclideanSpace_fin])
  let e : OpenPartialHomeomorph
      (Metric.sphere (0 : EuclideanSpace ℝ (Fin (n + 2))) 1)
      (EuclideanSpace ℝ (Fin (n + 1))) :=
    stereographic' (n + 1) (-v)
  have hv_source : v ∈ e.source := by
    simp [e, stereographic'_source, ne_neg_of_mem_unit_sphere ℝ v]
  have hv_zero : e v = 0 := by
    dsimp [e, stereographic']
    exact
      (OrthonormalBasis.fromOrthogonalSpanSingleton (𝕜 := ℝ) (n + 1)
          (ne_zero_of_mem_unit_sphere (-v))).repr.map_eq_zero_iff.mpr
        (stereographic_neg_apply v)
  have hs : ({v, -v}ᶜ : Set
      (Metric.sphere (0 : EuclideanSpace ℝ (Fin (n + 2))) 1)) ⊆ e.source := by
    intro x hx
    simp [e, stereographic'_source] at hx ⊢
    exact hx.2
  have himage :
      e '' ({v, -v}ᶜ : Set
        (Metric.sphere (0 : EuclideanSpace ℝ (Fin (n + 2))) 1)) =
        ({0}ᶜ : Set (EuclideanSpace ℝ (Fin (n + 1)))) := by
    ext y
    constructor
    · rintro ⟨x, hx, rfl⟩
      have hx_source : x ∈ e.source := hs hx
      simp at hx ⊢
      intro hy
      have hxeq : x = v := e.injOn hx_source hv_source (by simp [hv_zero, hy])
      exact hx.1 hxeq
    · intro hy
      have hy_ne_zero : y ≠ 0 := hy
      have hy_target : y ∈ e.target := by simp [e, stereographic'_target]
      refine ⟨e.symm y, ?_, e.right_inv hy_target⟩
      have hy_source : e.symm y ∈ e.source := e.map_target hy_target
      have hy_not_neg : e.symm y ≠ -v := by
        simpa [e, stereographic'_source] using hy_source
      have hy_not_v : e.symm y ≠ v := by
        intro hEq
        have : y = 0 := by rw [← e.right_inv hy_target, hEq, hv_zero]
        exact hy_ne_zero this
      simp [hy_not_v, hy_not_neg]
  exact ⟨e.homeomorphOfImageSubsetSource hs himage⟩




def standardSpherePole (k : ℕ) :
    Metric.sphere (0 : EuclideanSpace ℝ (Fin (k + 3))) 1 :=
  ⟨EuclideanSpace.single 0 1, by simp⟩


def standardSphereBasepoint (k : ℕ) :
    Metric.sphere (0 : EuclideanSpace ℝ (Fin (k + 3))) 1 :=
  ⟨EuclideanSpace.single 1 1, by simp⟩

private theorem standardSphereBasepoint_ne_pole (k : ℕ) :
    standardSphereBasepoint k ≠ standardSpherePole k := by
  intro h
  have h0 := congrArg
    (fun x : Metric.sphere (0 : EuclideanSpace ℝ (Fin (k + 3))) 1 =>
      (x : EuclideanSpace ℝ (Fin (k + 3))) 0) h
  simp [standardSphereBasepoint, standardSpherePole] at h0

private theorem standardSphereBasepoint_ne_neg_pole (k : ℕ) :
    standardSphereBasepoint k ≠ -standardSpherePole k := by
  intro h
  have h0 := congrArg
    (fun x : Metric.sphere (0 : EuclideanSpace ℝ (Fin (k + 3))) 1 =>
      (x : EuclideanSpace ℝ (Fin (k + 3))) 0) h
  simp [standardSphereBasepoint, standardSpherePole] at h0

private theorem standardSpherePole_ne_neg (k : ℕ) :
    standardSpherePole k ≠ -standardSpherePole k :=
  ne_neg_of_mem_unit_sphere ℝ (standardSpherePole k)

private theorem standardSphereComplement_isPathConnected
    (k : ℕ) (v : Metric.sphere (0 : EuclideanSpace ℝ (Fin (k + 3))) 1) :
    IsPathConnected ({v}ᶜ : Set
      (Metric.sphere (0 : EuclideanSpace ℝ (Fin (k + 3))) 1)) := by
  obtain ⟨e⟩ := sphereComplementHomeomorphEuclidean (n := k + 2) v
  letI : PathConnectedSpace
      ({v}ᶜ : Set (Metric.sphere (0 : EuclideanSpace ℝ (Fin (k + 3))) 1)) :=
    e.symm.surjective.pathConnectedSpace e.symm.continuous
  exact isPathConnected_iff_pathConnectedSpace.mpr inferInstance

private theorem standardSphereComplement_isSimplyConnected
    (k : ℕ) (v : Metric.sphere (0 : EuclideanSpace ℝ (Fin (k + 3))) 1) :
    IsSimplyConnected ({v}ᶜ : Set
      (Metric.sphere (0 : EuclideanSpace ℝ (Fin (k + 3))) 1)) := by
  obtain ⟨e⟩ := sphereComplementHomeomorphEuclidean (n := k + 2) v
  exact e.toHomotopyEquiv.simplyConnectedSpace

private theorem standardSphereTwoPointComplement_isPathConnected (k : ℕ) :
    IsPathConnected ({standardSpherePole k, -standardSpherePole k}ᶜ : Set
      (Metric.sphere (0 : EuclideanSpace ℝ (Fin (k + 3))) 1)) := by
  obtain ⟨e⟩ := sphereComplementTwoPointsHomeomorphPuncturedEuclidean
    (n := k + 1) (standardSpherePole k)
  have hrank :
      1 < Module.rank ℝ (EuclideanSpace ℝ (Fin (k + 2))) := by
    rw [← Module.finrank_eq_rank, finrank_euclideanSpace_fin]
    exact_mod_cast (show 1 < k + 2 by omega)
  have hpunc : IsPathConnected
      ({0}ᶜ : Set (EuclideanSpace ℝ (Fin (k + 2)))) :=
    isPathConnected_compl_singleton_of_one_lt_rank hrank 0
  letI : PathConnectedSpace
      ({0}ᶜ : Set (EuclideanSpace ℝ (Fin (k + 2)))) :=
    isPathConnected_iff_pathConnectedSpace.mp hpunc
  letI : PathConnectedSpace
      ({standardSpherePole k, -standardSpherePole k}ᶜ : Set
        (Metric.sphere (0 : EuclideanSpace ℝ (Fin (k + 3))) 1)) :=
    e.symm.surjective.pathConnectedSpace e.symm.continuous
  exact isPathConnected_iff_pathConnectedSpace.mpr inferInstance



def standardSpherePathConnectedOpenCover (k : ℕ) :
    PathConnectedOpenCover (standardSphereBasepoint k) Bool where
  carrier
    | false => {standardSpherePole k}ᶜ
    | true => {-standardSpherePole k}ᶜ
  isOpen i := by
    cases i <;> exact isOpen_compl_singleton
  cover := by
    intro x _
    by_cases hx : x = standardSpherePole k
    · refine Set.mem_iUnion.2 ⟨true, ?_⟩
      subst x
      exact standardSpherePole_ne_neg k
    · refine Set.mem_iUnion.2 ⟨false, ?_⟩
      exact hx
  base_mem i := by
    cases i
    · exact standardSphereBasepoint_ne_pole k
    · exact standardSphereBasepoint_ne_neg_pole k
  pathConnected i := by
    cases i
    · exact standardSphereComplement_isPathConnected k (standardSpherePole k)
    · exact standardSphereComplement_isPathConnected k (-standardSpherePole k)
  interPathConnected i j := by
    cases i <;> cases j
    · simpa [inter_self] using
        standardSphereComplement_isPathConnected k (standardSpherePole k)
    · rw [show {standardSpherePole k}ᶜ ∩ {-standardSpherePole k}ᶜ =
          {standardSpherePole k, -standardSpherePole k}ᶜ by
        ext x
        simp]
      exact standardSphereTwoPointComplement_isPathConnected k
    · rw [show {-standardSpherePole k}ᶜ ∩ {standardSpherePole k}ᶜ =
          {standardSpherePole k, -standardSpherePole k}ᶜ by
        ext x
        simp [and_comm]]
      exact standardSphereTwoPointComplement_isPathConnected k
    · simpa [inter_self] using
        standardSphereComplement_isPathConnected k (-standardSpherePole k)

private theorem standardSphereCover_isSimplyConnected (k : ℕ) :
    ∀ i, IsSimplyConnected ((standardSpherePathConnectedOpenCover k).carrier i) := by
  intro i
  cases i
  · exact standardSphereComplement_isSimplyConnected k (standardSpherePole k)
  · exact standardSphereComplement_isSimplyConnected k (-standardSpherePole k)


theorem standardSphereSimplyConnected (k : ℕ) :
    SimplyConnectedSpace
      (Metric.sphere (0 : EuclideanSpace ℝ (Fin (k + 3))) 1) := by
  have hpc : IsPathConnected
      (Metric.sphere (0 : EuclideanSpace ℝ (Fin (k + 3))) 1) := by
    have hrank : 1 < Module.rank ℝ (EuclideanSpace ℝ (Fin (k + 3))) := by
      rw [← Module.finrank_eq_rank, finrank_euclideanSpace_fin]
      exact_mod_cast (show 1 < k + 3 by omega)
    exact isPathConnected_sphere hrank 0 zero_le_one
  letI : PathConnectedSpace
      (Metric.sphere (0 : EuclideanSpace ℝ (Fin (k + 3))) 1) :=
    isPathConnected_iff_pathConnectedSpace.mp hpc
  exact simplyConnectedSpace_of_pathConnectedOpenCover
    (standardSpherePathConnectedOpenCover k)
    (standardSphereCover_isSimplyConnected k)


theorem sphereSimplyConnected_of_two_le {n : ℕ} (hn : 2 ≤ n) :
    SimplyConnectedSpace
      (Metric.sphere (0 : EuclideanSpace ℝ (Fin (n + 1))) 1) := by
  obtain ⟨k, rfl⟩ := Nat.exists_eq_add_of_le hn
  have hdim : 2 + k + 1 = k + 3 := by omega
  rw [hdim]
  exact standardSphereSimplyConnected k


end Poincare.Topology
