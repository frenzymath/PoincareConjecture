import PoincareConjecture.Proofs.M76.Horizon.Rigidity.IndexOne.Hierarchy.Cuts.RetainedCylinderPL
import PoincareConjecture.Proofs.M76.Horizon.Rigidity.IndexOne.Hierarchy.Cuts.PrismExtension
import PoincareConjecture.Proofs.M76.Horizon.Rigidity.IndexOne.Hierarchy.Regluing.PeriodHomeomorph









set_option autoImplicit false
open Set Metric Geometry

namespace PoincareConjecture.M76.HamiltonIntervalTorus.ExactSlabMeridian

local notation "V2" => (Fin 2 → ℝ)
local notation "V3" => (Fin 3 → ℝ)
local notation "D" => closedBall (0 : V2) 1
local notation "Q" => sphere (0 : V2) 1
local notation "I" => Icc (-1 : ℝ) 1
local notation "L" => hamiltonLowerPeriodLattice (Fin 2)
local notation "X" => LatticeHandleAmbient (Fin 1) (Fin 2) L
local notation "H" => LatticeHandle (Fin 1) (Fin 2) L
local notation "p" => (4 * (128 : ℝ))
local notation "C" => AddCircle p

private instance : Fact (0 < p) := ⟨by norm_num⟩

variable {α β : Type*} {e : α → OpenPartialHomeomorph X V3}
  {d : β → OpenPartialHomeomorph X V3} {phi : C(H, H)}
  {M : PairedMeridianHierarchy e d phi} {uv : ℝ × ℝ} (m : ExactSlabMeridian M uv)

private theorem periodMap_lateral
    (u : V2 × ℝ → X)
    (hlower : ∀ z ∈ D, u (z, m.width / 2) = m.product.map (z, (1 / 2 : ℝ)))
    (hupper : ∀ z ∈ D, u (z, p - m.width / 2) = m.product.map (z, -(1 / 2 : ℝ)))
    (hlateral : ∀ z ∈ Q, ∀ t ∈ Icc (m.width / 2) (p - m.width / 2),
      u (z, t) = m.retainedCylinderParameter (z, t))
    (z : Q) (t : ℝ) (ht : t ∈ Icc (0 : ℝ) p) :
    m.product.periodCutMap m.width p u (z, t) = m.retainedCylinderParameter (z, t) := by
  have hg : m.width / 2 < p - m.width / 2 := by linarith [m.width_small]
  have hzD : (z : V2) ∈ D := sphere_subset_closedBall z.property
  by_cases hlo : t ≤ m.width / 2
  · have hb := @periodLowerCoordinates_mapsTo m.width m.width_pos (z, t) ⟨hzD, ht.1, hlo⟩
    rw [periodLowerCoordinates_apply] at hb
    have hi : t / m.width ∈ I := ⟨by linarith [hb.2.1], by linarith [hb.2.2]⟩
    rw [m.product.periodCutMap_lower m.width p u hlo, periodLowerCoordinates_apply,
      m.product_marks_retainedCylinder z z.property _ hi, mul_div_cancel₀ _ m.width_pos.ne']
  · by_cases hup : p - m.width / 2 ≤ t
    · have hb := @periodUpperCoordinates_mapsTo m.width p m.width_pos (z, t) ⟨hzD, hup, ht.2⟩
      rw [periodUpperCoordinates_apply] at hb
      have hi : (t - p) / m.width ∈ I := ⟨by linarith [hb.2.1], by linarith [hb.2.2]⟩
      rw [m.product.periodCutMap_upper hg u hup, periodUpperCoordinates_apply,
        m.product_marks_retainedCylinder z z.property _ hi, mul_div_cancel₀ _ m.width_pos.ne',
        m.retainedCylinderParameter_apply z z.property (t - p),
        m.retainedCylinderParameter_apply z z.property t, AddCircle.coe_sub,
        AddCircle.coe_period, sub_zero]
    · have hmid : t ∈ Icc (m.width / 2) (p - m.width / 2) :=
        ⟨(not_le.mp hlo).le, (not_le.mp hup).le⟩
      rw [m.product.periodCutMap_middle m.width_pos hg u hlower hupper ⟨hzD, hmid⟩]
      exact hlateral z z.property t hmid




theorem exists_slab_parameter
    (hd : StandardLatticeHandleAtlas (Fin 1) (Fin 2) L d)
    (huv : uv ∈ ({(M.a, M.b), (M.b, M.a + p)} : Set (ℝ × ℝ))) :
    ∃ (G : (D × C) ≃ₜ sourceSlab M.eta uv.1 uv.2) (f : V2 × ℝ → X),
      PolyhedralPLInCharts e f (D ×ˢ Icc (0 : ℝ) p) ∧
      (∀ z : D, ∀ t ∈ Icc (0 : ℝ) p, (G (z, (t : C)) : X) = f (z, t)) ∧
      ∀ z : Q, ∀ t : C,
        (G (⟨z, sphere_subset_closedBall z.property⟩, t) : X) =
          m.frontierCylinderCoordinates (z, t) := by
  let : T2Space X := ((Homeomorph.refl (Fin 1 → ℝ)).prodCongr
    (hamiltonLowerLatticePiEquiv (Fin 2))).isEmbedding.t2Space
  let : ConnectedSpace X := ((Homeomorph.refl (Fin 1 → ℝ)).prodCongr
    (hamiltonLowerLatticePiEquiv (Fin 2))).connectedSpace_iff.mpr inferInstance
  have hopen : IsOpen ((Subtype.val : sourceSlab M.eta uv.1 uv.2 → X) ⁻¹'
      m.product.openStrip) := (m.product_open (1 / 2) (by norm_num) (by norm_num)).1
  have hg : m.width / 2 < p - m.width / 2 := by linarith [m.width_small]
  obtain ⟨HC, u, hu, huval, _, _, hlower, hupper, hlateral⟩ :=
    m.product.exists_marked_cut_prism_extension (M.slab_irreducible uv huv)
      (sourceSlab_isCompact M.eta uv.1 uv.2) hopen m.retainedCylinderParameter hg
      m.retainedCylinderParameter_lower m.retainedCylinderParameter_upper
      (m.retainedCylinderParameter_polyhedral hd huv) m.retainedCylinderParameter_injective
      m.retainedCylinderParameter_image
  obtain ⟨G, hPL, hwhole, _, _, _⟩ := m.product.exists_period_homeomorph
    (M.geometry.domains uv huv) (sourceSlab_isCompact M.eta uv.1 uv.2)
    hopen m.width_pos hg HC u hu huval hlower hupper
  refine ⟨G, m.product.periodCutMap m.width p u, hPL, hwhole, ?_⟩
  intro z t
  let s := AddCircle.equivIco p 0 t
  have hs : (s : ℝ) ∈ Icc (0 : ℝ) p :=
    ⟨s.property.1, by simpa only [zero_add] using s.property.2.le⟩
  have hst : ((s : ℝ) : C) = t := AddCircle.coe_equivIco
  rw [← hst, hwhole _ _ hs, m.periodMap_lateral u hlower hupper hlateral z s hs,
    m.retainedCylinderParameter_apply z z.property s]

end PoincareConjecture.M76.HamiltonIntervalTorus.ExactSlabMeridian
