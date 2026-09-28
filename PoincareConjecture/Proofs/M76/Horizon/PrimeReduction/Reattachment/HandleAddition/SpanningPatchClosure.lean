import PoincareConjecture.Proofs.M76.Horizon.PrimeReduction.Reattachment.HandleAddition.OriginalSpherePatchReplacement
import Mathlib.Topology.OpenPartialHomeomorph.IsImage









set_option autoImplicit false
open Set Geometry
namespace PoincareConjecture.M76
local notation "P2" => (ℝ × ℝ)
local notation "V3" => (Fin 3 → ℝ)
local notation "C3" => ((ℝ × ℝ) × ℝ)



theorem ChartwisePLSphere.original_disk_complement_eq_closure
    {X F ι : Type*} [TopologicalSpace X] [T2Space X]
    [NormedAddCommGroup F] [NormedSpace ℝ F] [FiniteDimensional ℝ F]
    {e : ι → OpenPartialHomeomorph X V3} {S : Set X}
    (s : ChartwisePLSphere e S)
    (he : ∀ i j,(e i).symm.trans (e j) ∈ piecewiseAffineGroupoid V3)
    {d q : Set F} (hd : IsFinitePLBallPair P2 d q)
    (p : F → X) (hp : PolyhedralPLInCharts e p d) (hpi : InjOn p d)
    (hpS : p '' d ⊆ S) (hout : (S \ p '' d).Nonempty) :
    S \ (p '' d \ p '' q) = closure (S \ p '' d) := by
  obtain ⟨k,r,hk,_,hg,hgi,himage,hrim⟩ := s.exists_original_disk_complement he hd p hp hpi hpS hout
  have hraw : s.map '' (k \ r) = S \ p '' d := by
    rw [hgi.image_sdiff_subset hk.1,himage,hrim]
    ext x
    have hq : x ∈ p '' q → x ∈ p '' d := fun h => image_mono hd.1 h
    simp only [mem_sdiff]
    tauto
  have hclosed : IsClosed (s.map '' k) := (hk.isCompact.image_of_continuousOn hg.continuousOn).isClosed
  have hdense : s.map '' k ⊆ closure (s.map '' (k \ r)) := by
    have hc : ContinuousOn s.map (closure (k \ r)) := hk.closure_sdiff.symm ▸ hg.continuousOn
    simpa only [hk.closure_sdiff] using hc.image_closure
  rw [←himage,←hraw]
  exact Subset.antisymm hdense (closure_minimal (image_mono sdiff_subset) hclosed)



theorem ChartwisePLSphere.original_ball_patch_replacement_eq_closures
    {X F ι : Type*} [TopologicalSpace X] [T2Space X]
    [NormedAddCommGroup F] [NormedSpace ℝ F] [FiniteDimensional ℝ F]
    {e : ι → OpenPartialHomeomorph X V3} {S Q T : Set X}
    (s : ChartwisePLSphere e S) (u : ChartwisePLBall e Q T)
    (he : ∀ i j,(e i).symm.trans (e j) ∈ piecewiseAffineGroupoid V3)
    {d q : Set F} (hd : IsFinitePLBallPair P2 d q)
    (p : F → X) (hp : PolyhedralPLInCharts e p d) (hpi : InjOn p d)
    (hcontact : Q ∩ S = p '' d) (hdT : p '' d ⊆ T)
    (hSout : (S \ p '' d).Nonempty) (hTout : (T \ p '' d).Nonempty) :
    (S \ (p '' d \ p '' q)) ∪ (T \ (p '' d \ p '' q)) =
      closure (S \ Q) ∪ closure (T \ S) := by
  obtain ⟨t⟩ := u.nonempty_boundarySphere
  rw [s.original_disk_complement_eq_closure he hd p hp hpi
    (hcontact.symm.subset.trans inter_subset_right) hSout,
    t.original_disk_complement_eq_closure he hd p hp hpi hdT hTout]
  have hS : S \ p '' d = S \ Q := by
    rw [←hcontact]
    ext x
    simp only [mem_sdiff,mem_inter_iff]
    tauto
  have hT : T \ p '' d = T \ S := by
    rw [←hcontact]
    ext x
    have hQ : x ∈ T → x ∈ Q := fun h => u.boundary_subset h
    simp only [mem_sdiff,mem_inter_iff]
    tauto
  rw [hS,hT]



theorem patch_closures_corner_model
    {X : Type*} [TopologicalSpace X]
    (H : OpenPartialHomeomorph X C3) {S Q : Set X}
    (hS : ∀ y ∈ H.source,y ∈ S ↔ (H y).1.1 = 0)
    (hQ : ∀ y ∈ H.source,y ∈ Q ↔ (H y).1.1 ≤ 0 ∧ (H y).1.2 ≤ 0) :
    ∀ y ∈ H.source,y ∈ closure (S \ Q) ∪ closure (frontier Q \ S) ↔
      ((H y).1.1 = 0 ∧ 0 ≤ (H y).1.2) ∨
      ((H y).1.2 = 0 ∧ (H y).1.1 ≤ 0) := by
  let Plane : Set C3 := (({0} : Set ℝ) ×ˢ univ) ×ˢ univ
  let Quad : Set C3 := (Iic (0 : ℝ) ×ˢ Iic (0 : ℝ)) ×ˢ univ
  have hs : H.IsImage S Plane := by
    intro y hy
    simpa only [Plane,mem_prod,mem_singleton_iff,mem_univ,and_true] using (hS y hy).symm
  have hq : H.IsImage Q Quad := by
    intro y hy
    simpa only [Quad,mem_prod,mem_Iic,mem_univ,and_true] using (hQ y hy).symm
  have hdiff1 : Plane \ Quad = (({0} : Set ℝ) ×ˢ Ioi 0) ×ˢ univ := by
    ext z
    simp only [Plane,Quad,mem_sdiff,mem_prod,mem_singleton_iff,mem_univ,and_true,mem_Iic,mem_Ioi]
    constructor
    · intro h
      exact ⟨h.1,lt_of_not_ge (fun hz => h.2 ⟨by rw [h.1],hz⟩)⟩
    · exact fun h => ⟨h.1,fun hn => (not_le_of_gt h.2) hn.2⟩
  have hdiff2 : frontier Quad \ Plane = (Iio (0 : ℝ) ×ˢ ({0} : Set ℝ)) ×ˢ univ := by
    dsimp only [Quad]
    rw [frontier_prod_univ_eq,frontier_prod_eq,frontier_Iic,closure_Iic]
    ext z
    simp only [Plane,mem_sdiff,mem_prod,mem_singleton_iff,mem_univ,and_true,mem_union,mem_Iic,mem_Iio]
    constructor
    · rintro ⟨h,hn⟩
      rcases h with h | h
      · exact ⟨lt_of_le_of_ne h.1 hn,h.2⟩
      · exact False.elim (hn h.1)
    · exact fun h => ⟨Or.inl ⟨h.1.le,h.2⟩,h.1.ne⟩
  have hc1 : closure (Plane \ Quad) = (({0} : Set ℝ) ×ˢ Ici 0) ×ˢ univ := by
    rw [hdiff1,closure_prod_eq,closure_prod_eq,closure_singleton,closure_Ioi,closure_univ]
  have hc2 : closure (frontier Quad \ Plane) = (Iic (0 : ℝ) ×ˢ ({0} : Set ℝ)) ×ˢ univ := by
    rw [hdiff2,closure_prod_eq,closure_prod_eq,closure_Iio,closure_singleton,closure_univ]
  have hh := (hs.diff hq).closure.union (hq.frontier.diff hs).closure
  intro y hy
  have h := (hh.apply_mem_iff hy).symm
  rw [hc1,hc2] at h
  simpa only [mem_union,mem_prod,mem_singleton_iff,mem_Iic,mem_Ici,mem_univ,and_true,true_and,and_comm] using h

end PoincareConjecture.M76
