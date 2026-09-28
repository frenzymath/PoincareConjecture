import PoincareConjecture.Proofs.M76.Mathlib.SquareShellRadius

set_option autoImplicit false

open Set Geometry

namespace SquareShell

theorem sectorMap_mem {a b : ℝ} (ha : 0 < a) (hb : 0 < b)
    {p : ℝ × ℝ} (hp : p ∈ parameterRectangle a b) : sectorMap a b p ∈ sector a b :=
  (sectorMap_image ha hb).subset (mem_image_of_mem _ hp)

theorem coordinate_eq_neg_radius_iff {a b r s : ℝ}
    (ha : 0 < a) (hb : 0 < b) (hr : r ∈ Icc a b) :
    coordinate a b s r = -r ↔ s = 0 := by
  constructor
  · intro h
    apply (strictMono_coordinate ha hb r).injective
    exact h.trans (coordinate_endpoints hr).1.symm
  · rintro rfl
    exact (coordinate_endpoints hr).1

theorem coordinate_eq_radius_iff {a b r s : ℝ}
    (ha : 0 < a) (hb : 0 < b) (hr : r ∈ Icc a b) :
    coordinate a b s r = r ↔ s = 1 := by
  constructor
  · intro h
    apply (strictMono_coordinate ha hb r).injective
    exact h.trans (coordinate_endpoints hr).2.symm
  · rintro rfl
    exact (coordinate_endpoints hr).2

theorem exists_sector_transport_with_parameters {a b c d : ℝ}
    (ha : 0 < a) (hab : a < b) (hc : 0 < c) (hcd : c < d) :
    ∃ e : sector a b ≃ₜ sector c d, e.IsFinitePL ∧
      ∀ p : parameterRectangle a b,
        (e ⟨sectorMap a b p, sectorMap_mem ha (ha.trans hab) p.property⟩ : ℝ × ℝ) =
          sectorMap c d ((p : ℝ × ℝ).1, radiusMap a b c d (p : ℝ × ℝ).2) := by
  obtain ⟨A, hA, hAval⟩ := exists_sector_homeomorph ha hab
  obtain ⟨B, hB, hBval⟩ := exists_sector_homeomorph hc hcd
  obtain ⟨D, hD, hDval⟩ := exists_parameter_radius_homeomorph hab hcd
  let e := A.symm.trans (D.trans B)
  refine ⟨e, hA.symm.trans (hD.trans hB), ?_⟩
  intro p
  have hinput :
      (⟨sectorMap a b p, sectorMap_mem ha (ha.trans hab) p.property⟩ : sector a b) = A p :=
    Subtype.ext (hAval p).symm
  rw [hinput]
  change (B (D (A.symm (A p))) : ℝ × ℝ) = _
  rw [A.symm_apply_apply, hBval, hDval]

theorem exists_sector_radius_homeomorph {a b c d : ℝ}
    (ha : 0 < a) (hab : a < b) (hc : 0 < c) (hcd : c < d) :
    ∃ e : sector a b ≃ₜ sector c d, e.IsFinitePL ∧
      ∀ x : sector a b,
        (e x : ℝ × ℝ).2 = radiusMap a b c d (x : ℝ × ℝ).2 ∧
        ((x : ℝ × ℝ).1 = -(x : ℝ × ℝ).2 ↔ (e x : ℝ × ℝ).1 = -(e x : ℝ × ℝ).2) ∧
        ((x : ℝ × ℝ).1 = (x : ℝ × ℝ).2 ↔ (e x : ℝ × ℝ).1 = (e x : ℝ × ℝ).2) ∧
        ((x : ℝ × ℝ).2 = a → (e x : ℝ × ℝ) = (c / a) • (x : ℝ × ℝ)) ∧
        ((x : ℝ × ℝ).2 = b → (e x : ℝ × ℝ) = (d / b) • (x : ℝ × ℝ)) := by
  obtain ⟨e, he, heparam⟩ := exists_sector_transport_with_parameters ha hab hc hcd
  refine ⟨e, he, ?_⟩
  intro x
  have hx : (x : ℝ × ℝ) ∈ sectorMap a b '' parameterRectangle a b := by
    rw [sectorMap_image ha (ha.trans hab)]
    exact x.property
  obtain ⟨p, hp, hpx⟩ := hx
  have hxval : (x : ℝ × ℝ) = sectorMap a b p := hpx.symm
  have hxsub : x = ⟨sectorMap a b p, sectorMap_mem ha (ha.trans hab) hp⟩ :=
    Subtype.ext hxval
  have heval : (e x : ℝ × ℝ) = sectorMap c d (p.1, radiusMap a b c d p.2) := by
    rw [hxsub]
    exact heparam ⟨p, hp⟩
  have hr : radiusMap a b c d p.2 ∈ Icc c d := by
    rw [← radiusMap_image hab hcd]
    exact mem_image_of_mem _ hp.2
  refine ⟨?_, ?_, ?_, ?_, ?_⟩
  · rw [hxval, heval]
    rfl
  · rw [hxval, heval]
    change coordinate a b p.1 p.2 = -p.2 ↔
      coordinate c d p.1 (radiusMap a b c d p.2) = -radiusMap a b c d p.2
    exact (coordinate_eq_neg_radius_iff ha (ha.trans hab) hp.2).trans
      (coordinate_eq_neg_radius_iff hc (hc.trans hcd) hr).symm
  · rw [hxval, heval]
    change coordinate a b p.1 p.2 = p.2 ↔
      coordinate c d p.1 (radiusMap a b c d p.2) = radiusMap a b c d p.2
    exact (coordinate_eq_radius_iff ha (ha.trans hab) hp.2).trans
      (coordinate_eq_radius_iff hc (hc.trans hcd) hr).symm
  · intro hxa
    have hpa : p.2 = a := by rw [hxval] at hxa; exact hxa
    rw [hxval, heval]
    change (coordinate c d p.1 (radiusMap a b c d p.2), radiusMap a b c d p.2) =
      (c / a) • (coordinate a b p.1 p.2, p.2)
    rw [hpa, (radiusMap_endpoints (c := c) (d := d) hab).1,
      coordinate_inner hcd.le hp.1, coordinate_inner hab.le hp.1]
    apply Prod.ext <;> dsimp <;> field_simp [ha.ne']
  · intro hxb
    have hpb : p.2 = b := by rw [hxval] at hxb; exact hxb
    rw [hxval, heval]
    change (coordinate c d p.1 (radiusMap a b c d p.2), radiusMap a b c d p.2) =
      (d / b) • (coordinate a b p.1 p.2, p.2)
    rw [hpb, (radiusMap_endpoints (c := c) (d := d) hab).2,
      coordinate_outer hcd.le hp.1, coordinate_outer hab.le hp.1]
    apply Prod.ext <;> dsimp <;> field_simp [(ha.trans hab).ne']

end SquareShell
