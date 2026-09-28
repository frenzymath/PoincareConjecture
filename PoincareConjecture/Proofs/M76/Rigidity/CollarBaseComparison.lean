import PoincareConjecture.Proofs.M76.Rigidity.InwardCollarCoordinates

set_option autoImplicit false

open Set Geometry

namespace Geometry

local notation "V3" => (Fin 3 → ℝ)

variable {E F X ι : Type*}
  [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
  [NormedAddCommGroup F] [NormedSpace ℝ F] [FiniteDimensional ℝ F]
  [TopologicalSpace X] {e : ι → OpenPartialHomeomorph X V3} {S : Set X}

theorem exists_finitePL_collar_base_comparison
    (hcompat : ∀ i j, (e i).symm.trans (e j) ∈ piecewiseAffineGroupoid V3)
    (L : SimplicialComplex ℝ E) (hL : L.faces.Finite)
    (K : SimplicialComplex ℝ F) (hK : K.faces.Finite)
    (HB : L.space ≃ₜ S) (HC : K.space ≃ₜ S)
    (c : E × ℝ → X) (d : F × ℝ → X)
    (hc : PolyhedralPLInCharts e c (L.space ×ˢ Icc (0 : ℝ) 1))
    (hd : PolyhedralPLInCharts e d (K.space ×ˢ Icc (0 : ℝ) 1))
    (hc0 : ∀ x : L.space, c ((x : E), 0) = HB x)
    (hd0 : ∀ y : K.space, d ((y : F), 0) = HC y) :
    ∃ Q : E → F, FinitePiecewiseAffineOn Q L.space ∧
      ∀ x : L.space, Q x = (HC.symm (HB x) : F) := by
  classical
  let Q : E → F := fun x => if hx : x ∈ L.space then HC.symm (HB ⟨x, hx⟩) else 0
  have hQval (x : L.space) : Q x = (HC.symm (HB x) : F) := by
    simp only [Q, dif_pos x.property]
  have hQcont : ContinuousOn Q L.space := by
    apply continuousOn_iff_continuous_domRestrict.mpr
    have h := continuous_subtype_val.comp (HC.symm.continuous.comp HB.continuous)
    convert h using 1
    funext x
    exact hQval x
  have hQmap : MapsTo Q L.space K.space := by
    intro x hx
    rw [hQval ⟨x, hx⟩]
    exact (HC.symm (HB ⟨x, hx⟩)).property
  have hcbase : PolyhedralPLInCharts e (fun z => c (z, 0)) L.space :=
    PolyhedralPLInCharts.finite_product_slice L hL hc ⟨le_rfl, zero_le_one⟩
  have hdbase : PolyhedralPLInCharts e (fun z => d (z, 0)) K.space :=
    PolyhedralPLInCharts.finite_product_slice K hK hd ⟨le_rfl, zero_le_one⟩
  have hdInj : InjOn (fun z => d (z, 0)) K.space := by
    intro x hx y hy hxy
    have hval : (HC ⟨x, hx⟩ : X) = HC ⟨y, hy⟩ :=
      (hd0 ⟨x, hx⟩).symm.trans (hxy.trans (hd0 ⟨y, hy⟩))
    exact congrArg Subtype.val (HC.injective (Subtype.ext hval))
  have hcomposite : PolyhedralPLInCharts e ((fun z => d (z, 0)) ∘ Q) L.space :=
    hcbase.congr (by
      intro x hx
      change c (x, 0) = d (Q x, 0)
      rw [hQval ⟨x, hx⟩, hd0, HC.apply_symm_apply]
      exact hc0 ⟨x, hx⟩)
  exact ⟨Q, hdbase.finitePiecewiseAffineOn_lift hcompat hdInj L hL
    hQcont hQmap hcomposite, hQval⟩

theorem isFinitePL_collar_base_transition
    (hcompat : ∀ i j, (e i).symm.trans (e j) ∈ piecewiseAffineGroupoid V3)
    (L : SimplicialComplex ℝ E) (hL : L.faces.Finite)
    (K : SimplicialComplex ℝ F) (hK : K.faces.Finite)
    (HB : L.space ≃ₜ S) (HC : K.space ≃ₜ S)
    (c : E × ℝ → X) (d : F × ℝ → X)
    (hc : PolyhedralPLInCharts e c (L.space ×ˢ Icc (0 : ℝ) 1))
    (hd : PolyhedralPLInCharts e d (K.space ×ˢ Icc (0 : ℝ) 1))
    (hc0 : ∀ x : L.space, c ((x : E), 0) = HB x)
    (hd0 : ∀ y : K.space, d ((y : F), 0) = HC y) :
    (HB.trans HC.symm).IsFinitePL ∧ (HB.trans HC.symm).symm.IsFinitePL := by
  obtain ⟨Q, hQ, hQval⟩ := exists_finitePL_collar_base_comparison
    hcompat L hL K hK HB HC c d hc hd hc0 hd0
  have hbeta : (HB.trans HC.symm).IsFinitePL :=
    ⟨Q, hQ, fun x => (hQval x).symm⟩
  exact ⟨hbeta, hbeta.symm⟩

end Geometry
