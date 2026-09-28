import PoincareConjecture.Proofs.M76.Horizon.Rigidity.Products.FailureArc.Neighborhood.Boundary.CyclicPanels.Fibers
import PoincareConjecture.Proofs.M76.Horizon.Dehn.Circles.SourceAnnulusPeriod
import PoincareConjecture.Proofs.M76.Horizon.Dehn.Circles.SourceAnnulusSquares



set_option autoImplicit false
open Set Geometry PLAnnularStrip

namespace PoincareConjecture.M76.Dehn.Annuli.CyclicPanels

local notation "P2" => (ℝ × ℝ)

theorem exists_original_annulus_of_periodic_strip
    {V X ι : Type*} [NormedAddCommGroup V] [NormedSpace ℝ V]
    [FiniteDimensional ℝ V] [TopologicalSpace X] [T2Space X]
    {e : ι → OpenPartialHomeomorph X V}
    (hcompat : ∀ i j, (e i).symm.trans (e j) ∈ piecewiseAffineGroupoid V)
    {L d : ℝ} (hd : 0 < d) (hwidth : 4 * d < L)
    (φ : P2 → X) (hφ : PolyhedralPLInCharts e φ (rectangle (4 * L) d))
    (hfib : ∀ x ∈ rectangle (4 * L) d, ∀ y ∈ rectangle (4 * L) d,
      φ x = φ y ↔ x.2 = y.2 ∧
        (x.1 : AddCircle (4 * L)) = (y.1 : AddCircle (4 * L))) :
    ∃ g : P2 → X, PolyhedralPLInCharts e g (squareAnnulus L d) ∧
      Topology.IsEmbedding (fun x : squareAnnulus L d => g x) ∧
      g '' squareAnnulus L d = φ '' rectangle (4 * L) d ∧
      (∀ s ∈ Icc 0 (4 * L), ∀ u : Icc (-d) d,
        g (annulusMap L (by linarith) ((s : AddCircle (4 * L)),u)) = φ (s,u)) ∧
      ∀ v ∈ Icc (-d) d,
        g '' {x ∈ squareAnnulus L d | depth L x = v} =
          φ '' (Icc 0 (4 * L) ×ˢ {v}) := by
  classical
  have hL : 0 < L := by linarith
  let : Fact (0 < 4 * L) := ⟨by linarith⟩
  have hend (u : Icc (-d) d) : φ (0,u) = φ (4 * L,u) :=
    (hfib _ ⟨⟨le_rfl,by positivity⟩,u.property⟩
      _ ⟨⟨by positivity,le_rfl⟩,u.property⟩).mpr
      ⟨rfl,by simp only [AddCircle.coe_zero,AddCircle.coe_period]⟩
  let a : AddCircle (4 * L) × Icc (-d) d → X := fun p =>
    AddCircle.liftIco (4 * L) 0 (fun s => φ (s,p.2)) p.1
  have ha (s : ℝ) (hs : s ∈ Icc 0 (4 * L)) (u : Icc (-d) d) :
      a ((s : AddCircle (4 * L)),u) = φ (s,u) :=
    AddCircle.liftIco_zero_coe_apply_Icc (hend u) hs
  have hac : Continuous a := by
    apply AddCircle.continuous_parametric_liftIco
      (fun p : ℝ × Icc (-d) d => φ (p.1,p.2))
    exacts [hφ.continuousOn.comp_continuous
      ((continuous_subtype_val.comp continuous_fst).prodMk
        (continuous_subtype_val.comp continuous_snd)) (fun p => ⟨p.1.property,p.2.property⟩),hend]
  have hrep (z : AddCircle (4 * L)) :
      ∃ s ∈ Icc 0 (4 * L), (s : AddCircle (4 * L)) = z := by
    exact ⟨AddCircle.equivIco (4 * L) 0 z,
      ⟨(AddCircle.equivIco (4 * L) 0 z).property.1,
        by simpa only [zero_add] using (AddCircle.equivIco (4 * L) 0 z).property.2.le⟩,
      AddCircle.coe_equivIco⟩
  have hai : Function.Injective a := by
    rintro ⟨z,u⟩ ⟨w,v⟩ h
    obtain ⟨s,hs,rfl⟩ := hrep z
    obtain ⟨t,ht,rfl⟩ := hrep w
    rw [ha s hs u,ha t ht v] at h
    have hh := (hfib _ ⟨hs,u.property⟩ _ ⟨ht,v.property⟩).mp h
    exact Prod.ext hh.2 (Subtype.ext hh.1)
  obtain ⟨E,g,_,hg,_,hperiod,hgemb⟩ :=
    _root_.Dehn.exists_square_annulus_map_of_period hcompat hd hwidth φ hφ a ha
  have hpoint (s : ℝ) (hs : s ∈ Icc 0 (4 * L)) (u : Icc (-d) d) :
      annulusMap L hL ((s : AddCircle (4 * L)),u) ∈ squareAnnulus L d :=
    _root_.Dehn.annulus_period_point_mem hd hwidth _ u
  have hdepth (s : ℝ) (u : Icc (-d) d) :
      depth L (annulusMap L hL ((s : AddCircle (4 * L)),u)) = u :=
    depth_annulusMap hL (lt_of_le_of_lt
      (mul_le_mul_of_nonneg_left (abs_le.mpr u.property) (by norm_num)) hwidth) _
  refine ⟨g,hg,hgemb ((hac.isClosedEmbedding hai).isEmbedding),?_,hperiod,?_⟩
  · ext y
    constructor
    · rintro ⟨x,hx,rfl⟩
      obtain ⟨s,hs,hxval⟩ := exists_period_parameter_of_depth hd hwidth ⟨x,hx⟩
      have hu := mem_squareAnnulus_iff_depth.mp hx
      exact ⟨(s,depth L x),⟨hs,hu⟩,
        (hperiod s hs ⟨depth L x,hu⟩).symm.trans (congrArg g hxval.symm)⟩
    · rintro ⟨⟨s,u⟩,⟨hs,hu⟩,rfl⟩
      exact ⟨_,hpoint s hs ⟨u,hu⟩,hperiod s hs ⟨u,hu⟩⟩
  · intro v hv
    ext y
    constructor
    · rintro ⟨x,⟨hx,hxv⟩,rfl⟩
      obtain ⟨s,hs,hxval⟩ := exists_period_parameter_of_depth hd hwidth ⟨x,hx⟩
      rw [hxv] at hxval
      exact ⟨(s,v),⟨hs,rfl⟩,(hperiod s hs ⟨v,hv⟩).symm.trans (congrArg g hxval.symm)⟩
    · rintro ⟨⟨s,u⟩,⟨hs,hu⟩,rfl⟩
      change u = v at hu
      subst u
      exact ⟨_,⟨hpoint s hs ⟨v,hv⟩,hdepth s ⟨v,hv⟩⟩,hperiod s hs ⟨v,hv⟩⟩

end PoincareConjecture.M76.Dehn.Annuli.CyclicPanels
