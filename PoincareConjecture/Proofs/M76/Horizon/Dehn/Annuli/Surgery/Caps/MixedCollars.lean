import PoincareConjecture.Proofs.M76.Horizon.Dehn.Annuli.Surgery.Caps.CylinderCap
import PoincareConjecture.Proofs.M76.Horizon.Dehn.Annuli.Surgery.Collars.RetainedContacts
import PoincareConjecture.Proofs.M76.Horizon.Dehn.Annuli.Surgery.Replacement.RetainedExteriors
import PoincareConjecture.Proofs.M76.Horizon.Dehn.Annuli.Parameters.RimCircleCoordinates









set_option autoImplicit false
open Set Metric Geometry PLAnnularStrip Topology
open _root_.Dehn

namespace PoincareConjecture.M76.Dehn.ProtectedAnnulus

local notation "V1" => (Fin 1 → ℝ)
local notation "V2" => (Fin 2 → ℝ)
local notation "V3" => (Fin 3 → ℝ)
local notation "P2" => (ℝ × ℝ)
local notation "Q" => sphere (0 : V2) 1
local notation "Cyl" => Set.prod Q (Icc (-1 : ℝ) 1)
local notation "Circle" => AddCircle (4 * (8 : ℝ))
local notation "Ann" => squareAnnulus 8 1

variable (L : Submodule ℤ V2) {α : Type*}
  {e : α → OpenPartialHomeomorph (LatticeHandleAmbient (Fin 1) (Fin 2) L) V3}
  {h : OpenPartialHomeomorph (V1 × V2) V3}
  (retained : HamiltonRetainedBlockChart (Fin 1) (Fin 2) L e h)
  {S : SimplicialComplex ℝ (V1 × V2)}
  {f : (V1 × V2) → chartShell L retained}
  {r : chartShell L retained → ℝ} {C : Set (chartShell L retained)}
  (s : Geometry.OriginalPLTower.Stage (fun _ : Unit ↦
    TopologicalSpace.Opens.openPartialHomeomorphSubtypeCoe
      (chartShell L retained) (chartShell_nonempty L retained)) S f r C)

theorem mixed_collar_tube_false
    (hS : S.space = source)
    (hvalues : ∀ x ∈ sphere (0 : V1) 1 ×ˢ Q, (f x : V3) = h (coordinates x))
    (period : Circle ≃ₜ Q) {l d : ℝ} (hd : 0 < d) (hwidth : 4 * d < l)
    (A : Fin 2 → Set P2) (B : ∀ k, OrientedPolygonCollar l d (A k)) (j : Fin 2)
    (hA : ∀ k, A k ⊆ {p : P2 | -1 < depth 8 p ∧ depth 8 p < 1})
    (henclosing : annulusSquare 8 1 ⊆ (B j).outer.inside)
    (hcontract : closure (B j.rev).outer.inside ⊆
      {p : P2 | -1 < depth 8 p ∧ depth 8 p < 1})
    (f₀ : P2 → s.Carrier) (hf₀ : PolyhedralPLInCharts s.charts f₀ Ann)
    (hwhole : ∀ b z, f₀ (annulusRimPoint b z) = s.annulusRim hS b (period z))
    (τ : (P2 × ℝ) → s.Carrier) (hτ : PolyhedralPLInCharts s.charts τ (identityTube l d))
    (hfib : ∀ z ∈ identityTube l d, ∀ w ∈ identityTube l d,
      τ z = τ w ↔ z.1 = w.1 ∧
        (z.2 : AddCircle (4 * l)) = (w.2 : AddCircle (4 * l)))
    (hvalue : ∀ (k : Fin 2) (t : ℝ) (_ht : t ∈ Icc 0 (4 * l)) (u : Icc (-d) d),
      f₀ ((B k).chart ⟨annulusMap l (by linarith) ((t : AddCircle (4 * l)), u),
        annulus_period_point_mem hd hwidth _ u⟩) = τ (sourceTubeDiagonal k u, t)) : False := by
  obtain ⟨oa, _, hoa, _, ho0, ho1, _⟩ := Annuli.exists_essential_collar_complement_annuli
    (B j) (hA j) henclosing (by norm_num) (by norm_num)
  obtain ⟨C₀, hC₀, hC₀v⟩ := Annuli.exists_selected_annulus_cylinder
  let O := annulusSquare 8 (-1) \ (B j).outer.inside
  let outer : Cyl ≃ₜ O := C₀.symm.trans oa
  have houter : outer.IsFinitePL := hC₀.symm.trans hoa
  have hOU : O ⊆ Ann := fun x hx ↦
    ((Annuli.essential_collar_retained_source_bounds (B j) (hA j) henclosing).1 x hx).1
  have hheight (x : Cyl) : x.val.2 = depth 8 (C₀.symm x : P2) := by
    simpa only [C₀.apply_symm_apply] using hC₀v (C₀.symm x)
  have hOend (x : Cyl) : x.val.2 = -1 ↔ depth 8 (outer x : P2) = -1 := by
    rw [hheight]
    exact ho0 (C₀.symm x)
  have hcontact := (Annuli.oriented_collar_retained_contacts (B j) (hA j)).1
  have hOA (x : Cyl) : (outer x : P2) ∈ A j ↔ x.val.2 = 1 := by
    rw [hheight]
    exact (show (outer x : P2) ∈ A j ↔ (outer x : P2) ∈ (B j).outer.boundary ℝ from
      ⟨fun hx ↦ hcontact.subset ⟨hx, (outer x).property⟩,
        fun hx ↦ (hcontact.symm.subset hx).1⟩).trans (ho1 (C₀.symm x)).symm
  obtain ⟨H, hH, hH0, hH1⟩ := Annuli.exists_square_annulus_cylinder_chart
    (L := l) hd (by linarith)
  let collar := H.trans (B j).chart
  have hcollar : collar.IsFinitePL := hH.trans (B j).chart_PL
  have hAO (x : Cyl) : (collar x : P2) ∈ O ↔ x.val.2 = -1 := by
    exact (show (collar x : P2) ∈ O ↔ (collar x : P2) ∈ (B j).outer.boundary ℝ from
      ⟨fun hx ↦ hcontact.subset ⟨(collar x).property, hx⟩,
        fun hx ↦ (hcontact.symm.subset hx).2⟩).trans
          (((B j).outer_depth (H x)).trans (hH0 x).symm)
  obtain ⟨q, _, hq⟩ := Annuli.exists_cylinder_end_comparison
    outer collar houter hcollar hOA hAO
  obtain ⟨a, _, ha, _, _, ha0, ha1⟩ := Annuli.exists_resolving_annulus_retained_seams
    s.charts s.compatible hd hwidth (b := d / 2) (by linarith) (by linarith)
    A (fun k ↦ (B k).chart) f₀ τ hτ hfib hvalue j
  let F₀ : C(Cyl, s.Carrier) := ⟨fun x ↦ f₀ (outer x),
    (hf₀.continuousOn.mono hOU).domRestrict.comp outer.continuous⟩
  let F₁ : C(Cyl, s.Carrier) := ⟨fun x ↦ a (H x),
    ha.continuousOn.domRestrict.comp H.continuous⟩
  have hseam (u : Q) : F₀ (Annuli.cylinderLevelPoint u 1) =
      F₁ (Annuli.cylinderLevelPoint (q u) 0) := by
    change f₀ (outer _) = a (H _)
    rw [ha0 _ ((hH0 _).mp (by norm_num [Annuli.cylinderLevelPoint]))]
    apply congrArg f₀
    convert (hq u).symm using 1 <;> norm_num [Annuli.cylinderLevelPoint, collar]
  let Dcap := closure (B j.rev).inner.inside
  have hcapS : Dcap ⊆ Ann := fun x hx ↦ mem_squareAnnulus_iff_depth.mpr
    ⟨(hcontract (subset_closure ((B j.rev).nested hx))).1.le,
      (hcontract (subset_closure ((B j.rev).nested hx))).2.le⟩
  let cap : C(Dcap, s.Carrier) := ⟨fun x ↦ f₀ x, (hf₀.continuousOn.mono hcapS).domRestrict⟩
  have hseamD (u : Q) : ((B j.rev).chart (H (Annuli.cylinderLevelPoint (q u) 1)) : P2) ∈
      Dcap := by
    have hh := ((B j.rev).inner_depth (H (Annuli.cylinderLevelPoint (q u) 1))).mpr
      ((hH1 _).mp (by norm_num [Annuli.cylinderLevelPoint]))
    have hh' := ((B j.rev).inner.frontier_closure_inside
      (B j.rev).inner_simplicial (B j.rev).inner_injective).symm ▸ hh
    simpa only [closure_closure] using hh'.1
  let seam : C(Q, Dcap) := ⟨fun u ↦
    ⟨(B j.rev).chart (H (Annuli.cylinderLevelPoint (q u) 1)), hseamD u⟩,
    (continuous_subtype_val.comp ((B j.rev).chart.continuous.comp
      (H.continuous.comp (Annuli.continuous_cylinderLevelPoint.comp
        (continuous_const.prodMk q.continuous))))).subtype_mk _⟩
  have hcap (u : Q) : F₁ (Annuli.cylinderLevelPoint (q u) 1) = cap (seam u) :=
    ha1 (H (Annuli.cylinderLevelPoint (q u) 1))
      ((hH1 _).mp (by norm_num [Annuli.cylinderLevelPoint]))
  have hnull := Annuli.cylinder_maps_nullhomotopic_of_cap
    ((B j.rev).inner.isFinitePLBallPair_closed_inside
      (B j.rev).inner_simplicial (B j.rev).inner_injective)
    F₀ F₁ q hseam cap seam hcap
  have hrim (u : Q) : (annulusRimPoint false (period.symm u) : P2) ∈ O := by
    have hh : depth 8 (annulusRimPoint false (period.symm u) : P2) = -1 :=
      depth_annulusRimPoint false (period.symm u)
    refine ⟨(mem_annulusSquare_iff 8 (-1) _).mpr hh.ge, ?_⟩
    intro hin
    have hlt := (mem_interior_annulusSquare_iff 8 (-1) _).mp
      ((Annuli.oriented_collar_disk_or_enclosing (B j) (hA j)).2.2.1 (subset_closure hin))
    linarith
  let rim : C(Q, O) := ⟨fun u ↦ ⟨annulusRimPoint false (period.symm u), hrim u⟩,
    ((continuous_subtype_val.comp (continuous_annulusRimPoint false)).comp
      period.symm.continuous).subtype_mk _⟩
  let p : C(Q, Q) := ⟨fun u ↦ ⟨(outer.symm (rim u)).val.1, (outer.symm (rim u)).property.1⟩,
    (continuous_fst.comp (continuous_subtype_val.comp
      (outer.symm.continuous.comp rim.continuous))).subtype_mk _⟩
  have hp (u : Q) : Annuli.cylinderLevelPoint (p u) 0 = outer.symm (rim u) := by
    have hh := (hOend (outer.symm (rim u))).mpr (by
      rw [outer.apply_symm_apply]
      exact depth_annulusRimPoint false (period.symm u))
    apply Subtype.ext
    exact Prod.ext rfl (by simpa [Annuli.cylinderLevelPoint] using hh.symm)
  have hn := hnull.comp_left p
  have heq : (⟨fun u ↦ F₀ (Annuli.cylinderLevelPoint u 0),
      F₀.continuous.comp (Annuli.continuous_cylinderLevelPoint.comp
        (continuous_const.prodMk continuous_id))⟩ : C(Q, s.Carrier)).comp p =
      s.annulusRim hS false := by
    ext u
    change f₀ (outer (Annuli.cylinderLevelPoint (p u) 0)) = _
    rw [hp, outer.apply_symm_apply]
    change f₀ (annulusRimPoint false (period.symm u)) = _
    rw [hwhole, period.apply_symm_apply]
  rw [heq] at hn
  exact stage_rim_not_nullhomotopic L retained s hS hvalues false hn

end PoincareConjecture.M76.Dehn.ProtectedAnnulus
