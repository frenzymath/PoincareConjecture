import PoincareConjecture.Proofs.M76.Horizon.Dehn.Circles.AnnulusPeriodMap
import PoincareConjecture.Proofs.M76.Horizon.Dehn.Circles.AnnulusBoundaryParameters
import PoincareConjecture.Proofs.M76.Mathlib.PolyhedralPLFixedChart








set_option autoImplicit false
open Set Geometry PLAnnularStrip

namespace Dehn

theorem exists_finite_square_annulus_complex {L d : ℝ}
    (hd : 0 < d) (hwidth : 4 * d < L) :
    ∃ K : SimplicialComplex ℝ (ℝ × ℝ), K.faces.Finite ∧ K.space = squareAnnulus L d := by
  have hpiece (i : Fin 4) : ∃ K : SimplicialComplex ℝ (ℝ × ℝ),
      K.faces.Finite ∧ K.space = stripRegion L d i := by
    obtain ⟨c, hc, _⟩ := exists_rotated_strip_charts hd hwidth i
    obtain ⟨_, ⟨K, hK, hKs, _⟩, _⟩ := hc.symm
    exact ⟨K, hK, hKs⟩
  choose K hK hKs using hpiece
  obtain ⟨A, hA, hAs, _⟩ := SimplicialComplex.exists_finite_triangulation_iUnion K hK
  refine ⟨A, hA, hAs.trans ?_⟩
  simp only [hKs]
  rw [← union_four_strips hd.le (show 2 * d < L by linarith)]
  ext x
  simp [Fin.exists_fin_succ, or_assoc, stripRegion]

theorem annulus_period_point_mem {L d : ℝ} (hd : 0 < d) (hwidth : 4 * d < L)
    (s : AddCircle (4 * L)) (u : Icc (-d) d) :
    annulusMap L (by linarith) (s, u) ∈ squareAnnulus L d := by
  apply mem_squareAnnulus_iff_depth.mpr
  rw [depth_annulusMap (by linarith)
    (lt_of_le_of_lt (mul_le_mul_of_nonneg_left (abs_le.mpr u.property) (by norm_num)) hwidth)]
  exact u.property

theorem exists_finitePL_annulus_of_periodic_strip
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
    {L d : ℝ} (hd : 0 < d) (hwidth : 4 * d < L)
    (φ : (ℝ × ℝ) → E) (hφ : FinitePiecewiseAffineOn φ (rectangle (4 * L) d))
    (hfib : ∀ x ∈ rectangle (4 * L) d, ∀ y ∈ rectangle (4 * L) d,
      φ x = φ y ↔ x.2 = y.2 ∧
        (x.1 : AddCircle (4 * L)) = (y.1 : AddCircle (4 * L))) :
    ∃ c : squareAnnulus L d ≃ₜ (φ '' rectangle (4 * L) d),
      c.IsFinitePL ∧ c.symm.IsFinitePL ∧
      (∀ (s : ℝ) (_hs : s ∈ Icc 0 (4 * L)) (u : Icc (-d) d),
        (c ⟨annulusMap L (by linarith) ((s : AddCircle (4 * L)), u),
          annulus_period_point_mem hd hwidth _ u⟩ : E) = φ (s, u)) ∧
      ∀ p : squareAnnulus L d, ∀ s ∈ Icc 0 (4 * L),
        (p : ℝ × ℝ) = annulusMap L (by linarith)
          ((s : AddCircle (4 * L)), depth L p) →
        (c p : E) = φ (s, depth L p) := by
  classical
  have hL : 0 < L := by linarith
  let : Fact (0 < 4 * L) := ⟨by positivity⟩
  have hend (u : Icc (-d) d) : φ (0, u) = φ (4 * L, u) :=
    (hfib _ ⟨⟨le_rfl, by positivity⟩, u.property⟩
      _ ⟨⟨by positivity, le_rfl⟩, u.property⟩).mpr
        ⟨rfl, by simp only [AddCircle.coe_zero, AddCircle.coe_period]⟩
  let a : AddCircle (4 * L) × Icc (-d) d → E := fun p ↦
    AddCircle.liftIco (4 * L) 0 (fun s ↦ φ (s, p.2)) p.1
  have ha (s : ℝ) (hs : s ∈ Icc 0 (4 * L)) (u : Icc (-d) d) :
      a ((s : AddCircle (4 * L)), u) = φ (s, u) :=
    AddCircle.liftIco_zero_coe_apply_Icc (hend u) hs
  have hac : Continuous a := by
    apply AddCircle.continuous_parametric_liftIco
      (fun p : ℝ × Icc (-d) d ↦ φ (p.1, p.2))
    exacts [hφ.continuousOn.comp_continuous
      ((continuous_subtype_val.comp continuous_fst).prodMk
        (continuous_subtype_val.comp continuous_snd)) (fun p ↦ ⟨p.1.property, p.2.property⟩), hend]
  have hrep (z : AddCircle (4 * L)) : ∃ s ∈ Icc 0 (4 * L), (s : AddCircle (4 * L)) = z := by
    exact ⟨AddCircle.equivIco (4 * L) 0 z,
      ⟨(AddCircle.equivIco (4 * L) 0 z).property.1,
        by simpa only [zero_add] using (AddCircle.equivIco (4 * L) 0 z).property.2.le⟩,
      AddCircle.coe_equivIco⟩
  have hai : Function.Injective a := by
    rintro ⟨z, u⟩ ⟨w, v⟩ h
    obtain ⟨s, hs, rfl⟩ := hrep z
    obtain ⟨t, ht, rfl⟩ := hrep w
    rw [ha s hs u, ha t ht v] at h
    obtain ⟨huv, hst⟩ := (hfib _ ⟨hs, u.property⟩ _ ⟨ht, v.property⟩).mp h
    exact Prod.ext hst (Subtype.ext huv)
  let e : Unit → OpenPartialHomeomorph E E := fun _ ↦ OpenPartialHomeomorph.refl E
  have hcompat : ∀ i j, (e i).symm.trans (e j) ∈ piecewiseAffineGroupoid E := by
    intro i j
    exact StructureGroupoid.trans _ (StructureGroupoid.symm _
      (StructureGroupoid.id_mem _)) (StructureGroupoid.id_mem _)
  obtain ⟨K, hK, hKs, hAff⟩ := hφ
  have hφPL : PolyhedralPLInCharts e φ (rectangle (4 * L) d) := by
    have hh := polyhedralPLInCharts_of_one_chart_inverse (e := e) K hK
      (show FinitePiecewiseAffineOn φ K.space from ⟨K, hK, rfl, hAff⟩) ()
      (fun _ _ ↦ mem_univ _)
    simpa only [e, OpenPartialHomeomorph.refl_symm, OpenPartialHomeomorph.refl_apply,
      Function.id_comp, hKs] using hh
  obtain ⟨A, g, hA, hgPL, hgA, hgperiod, hgemb⟩ :=
    exists_square_annulus_map_of_period hcompat hd hwidth φ hφPL a ha
  have hgembedding := hgemb ((hac.isClosedEmbedding hai).isEmbedding)
  obtain ⟨J, hJ, hJs⟩ := exists_finite_square_annulus_complex hd hwidth
  have hg : FinitePiecewiseAffineOn g (squareAnnulus L d) := by
    have hh := (hJs.symm ▸ hgPL).finitePiecewiseAffineOn_fixed_chart hcompat J hJ ()
      (fun _ _ ↦ mem_univ _)
    simpa only [e, OpenPartialHomeomorph.refl_apply, Function.id_comp, hJs] using hh
  have hgi : InjOn g (squareAnnulus L d) := by
    intro x hx y hy hxy
    exact congrArg Subtype.val (hgembedding.injective (show
      (fun p : squareAnnulus L d ↦ g p) ⟨x, hx⟩ =
        (fun p : squareAnnulus L d ↦ g p) ⟨y, hy⟩ from hxy))
  have himage : g '' squareAnnulus L d = φ '' rectangle (4 * L) d := by
    ext y
    constructor
    · rintro ⟨x, hx, rfl⟩
      obtain ⟨s, hs, hxval⟩ := exists_period_parameter_of_depth hd hwidth ⟨x, hx⟩
      have hu := mem_squareAnnulus_iff_depth.mp hx
      exact ⟨(s, depth L x), ⟨hs, hu⟩,
        (hgperiod s hs ⟨depth L x, hu⟩).symm.trans (congrArg g hxval.symm)⟩
    · rintro ⟨⟨s, u⟩, ⟨hs, hu⟩, rfl⟩
      exact ⟨A ((s : AddCircle (4 * L)), ⟨u, hu⟩),
        (A ((s : AddCircle (4 * L)), ⟨u, hu⟩)).property,
        (hgA _).trans (ha s hs ⟨u, hu⟩)⟩
  obtain ⟨c, hc, hcval⟩ := hg.exists_homeomorph_image hgi
  let c' := c.trans (Homeomorph.setCongr himage)
  have hc' : c'.IsFinitePL := by
    obtain ⟨f, hf, hfval⟩ := hc
    exact ⟨f, hf, hfval⟩
  refine ⟨c', hc', hc'.symm, ?_, ?_⟩
  · intro s hs u
    exact (hcval _).trans (hgperiod s hs u)
  · intro p s hs hp
    exact (hcval p).trans ((congrArg g hp).trans
      (hgperiod s hs ⟨depth L p, mem_squareAnnulus_iff_depth.mp p.property⟩))

end Dehn
