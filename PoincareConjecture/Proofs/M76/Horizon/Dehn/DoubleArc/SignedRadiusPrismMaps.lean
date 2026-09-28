import PoincareConjecture.Proofs.M76.Horizon.Dehn.DoubleArc.SignedRadiusPrism








set_option autoImplicit false

open Set Geometry

namespace PoincareConjecture.M76.Dehn

local notation "P2" => (ℝ × ℝ)

theorem exists_signed_radius_prism_map
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
    (i : Fin 2) (sign : Bool) (α β : ℝ) (hαβ : α < β)
    {F Axis Outer : Set E} (D : Bool → Set E) (A C : Bool → E)
    (hF : IsFinitePLBallPair P2 F (Axis ∪ Outer))
    (hAxis : IsFinitePLBallPair ℝ Axis {A false, A true})
    (hOuter : IsFinitePLBallPair ℝ Outer {A false, A true})
    (hInter : Axis ∩ Outer = {A false, A true})
    (hD : ∀ j, IsFinitePLBallPair ℝ (D j) {A j, C j})
    (hDO : ∀ j, D j ⊆ Outer)
    (hA : A false ≠ A true) (hAC : ∀ j, A j ≠ C j)
    (hDis : Disjoint (D false) (D true))
    (z : Icc α β ≃ₜ Axis) (hz : z.IsFinitePL)
    (hz0 : (z ⟨α, le_rfl, hαβ.le⟩ : E) = A false)
    (hz1 : (z ⟨β, hαβ.le, le_rfl⟩ : E) = A true)
    (e : ∀ j, signedTubeRadius i sign ≃ₜ D j)
    (he : ∀ j, (e j).IsFinitePL)
    (hea : ∀ j, (e j ⟨(0, 0), left_mem_segment ℝ _ _⟩ : E) = A j)
    (hec : ∀ j, (e j ⟨signedTubeCorner i sign, right_mem_segment ℝ _ _⟩ : E) = C j) :
    ∃ H : ↥(signedTubeRadius i sign ×ˢ Icc α β) ≃ₜ F, H.IsFinitePL ∧
      (∀ t : Icc α β,
        (H ⟨((0, 0), t), left_mem_segment ℝ _ _, t.property⟩ : E) = z t) ∧
      (∀ j (x : signedTubeRadius i sign),
        (H ⟨(x, if j then β else α), x.property,
          by cases j <;> simp [hαβ.le]⟩ : E) = e j x) ∧
      (∀ x : ↥(signedTubeRadius i sign ×ˢ Icc α β),
        (x : P2 × ℝ) ∈ signedTubePrismAxis α β ↔ (H x : E) ∈ Axis) ∧
      (∀ x : ↥(signedTubeRadius i sign ×ˢ Icc α β),
        (x : P2 × ℝ) ∈ signedTubePrismOuter i sign α β ↔ (H x : E) ∈ Outer) ∧
      ∀ j (x : ↥(signedTubeRadius i sign ×ˢ Icc α β)),
        (x : P2 × ℝ) ∈ signedTubeRadius i sign ×ˢ {if j then β else α} ↔
        (H x : E) ∈ D j := by
  let r := signedTubeRadius i sign
  let corner := signedTubeCorner i sign
  let time := fun j : Bool => if j then β else α
  let d := fun j : Bool => r ×ˢ {time j}
  let a := fun j : Bool => (((0, 0) : P2), time j)
  let c := fun j : Bool => (corner, time j)
  have htime (j : Bool) : time j ∈ Icc α β := by
    cases j <;> simp [time, hαβ.le]
  have hd (j : Bool) : IsFinitePLBallPair ℝ (d j) {a j, c j} :=
    signedTubePrism_end_ball i sign (time j)
  have hdo (j : Bool) : d j ⊆ signedTubePrismOuter i sign α β := by
    rintro x ⟨hx, ht⟩
    refine Or.inr ⟨hx, ?_⟩
    cases j
    · exact Or.inl ht
    · exact Or.inr ht
  have ha : a false ≠ a true := fun h => hαβ.ne (congrArg Prod.snd h)
  have hac (j : Bool) : a j ≠ c j := fun h =>
    signedTube_corner_ne_center i sign (congrArg Prod.fst h).symm
  have hdis : Disjoint (d false) (d true) := disjoint_left.mpr
    (fun x hx hy => hαβ.ne (hx.2.symm.trans hy.2))
  let z' := (signedTubePrismAxisProjection α β).trans z
  let e' := fun j : Bool => (signedTubePrismEndProjection i sign (time j)).trans (e j)
  have hz' : z'.IsFinitePL := (signedTubePrismAxisProjection_isFinitePL α β hαβ).trans hz
  have he' (j : Bool) : (e' j).IsFinitePL :=
    (signedTubePrismEndProjection_isFinitePL i sign (time j)).trans (he j)
  have haxis : IsFinitePLBallPair ℝ (signedTubePrismAxis α β) {a false, a true} :=
    signedTubePrism_axis_ball α β hαβ
  have hza (j : Bool) : (z' ⟨a j, haxis.1 (by cases j <;> simp)⟩ : E) = A j := by
    cases j
    · exact hz0
    · exact hz1
  have hea' (j : Bool) : (e' j ⟨a j, (hd j).1 (Or.inl rfl)⟩ : E) = A j := hea j
  have hec' (j : Bool) : (e' j ⟨c j, (hd j).1 (Or.inr rfl)⟩ : E) = C j := hec j
  obtain ⟨hprism, houter, hinter⟩ := signedTubePrism_boundary i sign α β hαβ
  obtain ⟨H, hH, hkeepAxis, hkeepEnds, hAxisMem, hOuterMem, hEndMem⟩ :=
    exists_signed_half_face_map d D a c A C hprism hF haxis hAxis houter hOuter
      hinter hInter hd hD hdo hDO ha hA hac hAC hdis hDis z' hz' hza e' he' hea' hec'
  refine ⟨H, hH, ?_, ?_, hAxisMem, hOuterMem, hEndMem⟩
  · intro t
    exact hkeepAxis ⟨((0, 0), t), rfl, t.property⟩
  · intro j x
    exact hkeepEnds j ⟨(x, time j), x.property, rfl⟩

end PoincareConjecture.M76.Dehn
