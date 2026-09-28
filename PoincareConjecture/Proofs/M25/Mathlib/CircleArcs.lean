import Mathlib.Analysis.InnerProductSpace.PiL2
import Mathlib.Analysis.SpecialFunctions.Complex.Circle
import Mathlib.Topology.Connected.Clopen
import Mathlib.Topology.OpenPartialHomeomorph.IsImage











set_option autoImplicit false

open Set

namespace AddCircle

variable (p : ℝ) [Fact (0 < p)]




theorem compl_image_Ioo_eq_image_Icc (a b : ℝ) (hab : a < b) (hbp : b < a + p) :
    (((↑) : ℝ → AddCircle p) '' Ioo a b)ᶜ =
      ((↑) : ℝ → AddCircle p) '' Icc b (a + p) := by
  ext z
  constructor
  · intro hz
    obtain ⟨x, hx, rfl⟩ :=
      show z ∈ ((↑) : ℝ → AddCircle p) '' Ico a (a + p) from
        (coe_image_Ico_eq p a).symm ▸ mem_univ z
    by_cases hxa : x = a
    · subst x
      exact ⟨a + p, ⟨hbp.le, le_rfl⟩, coe_add_period p a⟩
    · have hax : a < x := lt_of_le_of_ne hx.1 (Ne.symm hxa)
      have hbx : b ≤ x := by
        by_contra h
        exact hz ⟨x, ⟨hax, lt_of_not_ge h⟩, rfl⟩
      exact ⟨x, ⟨hbx, hx.2.le⟩, rfl⟩
  · rintro ⟨x, hx, rfl⟩ ⟨y, hy, hxy⟩
    have hyI : y ∈ Ico a (a + p) := ⟨hy.1.le, hy.2.trans hbp⟩
    by_cases hxp : x = a + p
    · subst x
      have hya : y = a :=
        (coe_eq_coe_iff_of_mem_Ico hyI
          ⟨le_rfl, lt_add_of_pos_right a (Fact.out : 0 < p)⟩).mp
            (hxy.trans (coe_add_period p a))
      exact (ne_of_gt hy.1) hya
    · have hxI : x ∈ Ico a (a + p) :=
        ⟨hab.le.trans hx.1, lt_of_le_of_ne hx.2 hxp⟩
      have hyx : y = x := (coe_eq_coe_iff_of_mem_Ico hyI hxI).mp hxy
      exact (not_lt_of_ge hx.1) (hyx ▸ hy.2)




theorem isConnected_compl_image_Ioo (a b : ℝ) (hab : a < b) (hbp : b < a + p) :
    IsConnected ((((↑) : ℝ → AddCircle p) '' Ioo a b)ᶜ) := by
  rw [compl_image_Ioo_eq_image_Icc p a b hab hbp]
  exact (isConnected_Icc hbp.le).image _ (AddCircle.continuous_mk' p).continuousOn



theorem isOpen_image_Ioo (a b : ℝ) (hbp : b ≤ a + p) :
    IsOpen (((↑) : ℝ → AddCircle p) '' Ioo a b) := by
  apply (openPartialHomeomorphCoe p a).isOpen_image_of_subset_source isOpen_Ioo
  intro x hx
  exact ⟨hx.1, hx.2.trans_le hbp⟩




theorem exists_openPartialHomeomorph_Ioo (a b : ℝ) (hbp : b ≤ a + p) :
    ∃ e : OpenPartialHomeomorph ℝ (AddCircle p),
      e.source = Ioo a b ∧ e.target = ((↑) : ℝ → AddCircle p) '' Ioo a b ∧
      ∀ s : ℝ, e s = (s : AddCircle p) := by
  let e := (openPartialHomeomorphCoe p a).restr (Ioo a b)
  have hsource : e.source = Ioo a b := by
    rw [OpenPartialHomeomorph.restr_source' _ _ isOpen_Ioo]
    apply inter_eq_right.mpr
    intro x hx
    exact ⟨hx.1, hx.2.trans_le hbp⟩
  have hfun : (e : ℝ → AddCircle p) = (↑) := rfl
  refine ⟨e, hsource, ?_, fun _ => rfl⟩
  rw [← e.image_source_eq_target, hsource, hfun]

end AddCircle

namespace Circle




noncomputable def euclideanHomeomorph :
    Circle ≃ₜ Metric.sphere (0 : EuclideanSpace ℝ (Fin 2)) 1 :=
  Complex.orthonormalBasisOneI.repr.toHomeomorph.subtype fun z => by
    change z ∈ Metric.sphere (0 : ℂ) 1 ↔ Complex.orthonormalBasisOneI.repr z ∈
      Metric.sphere (0 : EuclideanSpace ℝ (Fin 2)) 1
    simp only [Metric.mem_sphere, dist_zero_right, LinearIsometryEquiv.norm_map]

end Circle

namespace AddCircle



noncomputable def euclideanCircleHomeomorph (p : ℝ) (hp : p ≠ 0) :
    AddCircle p ≃ₜ Metric.sphere (0 : EuclideanSpace ℝ (Fin 2)) 1 :=
  (homeomorphCircle hp).trans Circle.euclideanHomeomorph

end AddCircle
