import PoincareConjecture.Proofs.Horizon.Topology.Manifold.NeckCap.ProjectiveDouble.Collar
import PoincareConjecture.Proofs.Horizon.Topology.Manifold.NeckCap.ProjectiveDouble.Monodromy
import PoincareConjecture.Proofs.Horizon.AlgebraicTopology.FundamentalGroup.VanKampen.Extension
import PoincareConjecture.Proofs.Horizon.AlgebraicTopology.FundamentalGroup.VanKampen.Collar

noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

open Set
open scoped Manifold ContDiff Topology

namespace PoincareConjecture.SmoothProjectiveDoubleModel

private theorem not_finite_of_dihedral_reflections {G : Type*} [Group G]
    (f : G →* DihedralGroup 0)
    (hzero : DihedralGroup.sr 0 ∈ f.range) (hone : DihedralGroup.sr 1 ∈ f.range) :
    ¬ Finite G := by
  intro hfinite
  let : Finite G := hfinite
  have hr : DihedralGroup.r 1 ∈ f.range := by
    simpa only [DihedralGroup.sr_mul_sr, sub_zero] using f.range.mul_mem hzero hone
  have hk (k : ℤ) : DihedralGroup.r (k : ZMod 0) ∈ f.range := by
    have he : (DihedralGroup.r (1 : ZMod 0)) ^ k = DihedralGroup.r (k : ZMod 0) := by
      rw [DihedralGroup.r_zpow, one_mul]
      rfl
    rw [← he]
    exact f.range.zpow_mem hr k
  let : Finite f.range := Finite.of_surjective f.rangeRestrict f.rangeRestrict_surjective
  have hi : Function.Injective (fun k : ℤ =>
      (⟨DihedralGroup.r (k : ZMod 0), hk k⟩ : f.range)) := by
    intro a b h
    exact DihedralGroup.r.inj (congrArg Subtype.val h)
  let : Finite ℤ := Finite.of_injective _ hi
  exact not_finite ℤ

variable {M : Type*} [TopologicalSpace M]
  [ChartedSpace (EuclideanSpace ℝ (Fin 3)) M]

theorem exists_infinite_fundamentalGroup (D : SmoothProjectiveDoubleModel M) :
    ∃ b : M, Infinite (FundamentalGroup M b) := by
  let U := D.first_region ∪ D.collarRegion
  let V := D.second_region ∪ D.collarRegion
  have hU : IsOpen U := D.first_open.union D.collar_open
  have hV : IsOpen V := D.second_open.union D.collar_open
  have hUV : IsSimplyConnected (U ∩ V) := by
    change IsSimplyConnected
      ((D.first_region ∪ D.collarRegion) ∩ (D.second_region ∪ D.collarRegion))
    rw [D.enlarged_inter]
    exact D.collarRegion_simplyConnected
  obtain ⟨b, hb⟩ := D.collarRegion_simplyConnected.nonempty
  let bU : U := ⟨b, Or.inr hb⟩
  let bV : V := ⟨b, Or.inr hb⟩
  obtain ⟨f, hf⟩ := VanKampen.exists_hom_mem_range_of_union D.first_region D.collarRegion
    D.first_open D.collar_open D.collarRegion_simplyConnected.isPathConnected
    D.first_inter_collarRegion_simplyConnected (DihedralGroup.sr 0)
    (fun x => D.first_model.exists_dihedral_reflection_monodromy x 0) bU hb
  obtain ⟨g, hg⟩ := VanKampen.exists_hom_mem_range_of_union D.second_region D.collarRegion
    D.second_open D.collar_open D.collarRegion_simplyConnected.isPathConnected
    D.second_inter_collarRegion_simplyConnected (DihedralGroup.sr 1)
    (fun x => D.second_model.exists_dihedral_reflection_monodromy x 1) bV hb
  obtain ⟨φ, hφf, hφg⟩ := VanKampen.exists_hom_range_contains U V hUV bU
    (Or.inr hb) hU hV D.enlarged_cover f g
  exact ⟨b, not_finite_iff_infinite.mp
    (not_finite_of_dihedral_reflections φ (hφf hf) (hφg hg))⟩

end PoincareConjecture.SmoothProjectiveDoubleModel
