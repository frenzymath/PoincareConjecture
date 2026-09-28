import PoincareConjecture.Proofs.M76.Horizon.Rigidity.IndexOne.Cutting.RelativeCorner
import PoincareConjecture.Proofs.M76.Brown.RelativeHalfspaceCharts

set_option autoImplicit false
open Set Geometry BrownCollar

namespace PoincareConjecture.M76.HamiltonIntervalTorus

theorem exists_local_collar_of_quadrant_chart
    {X E : Type*} [TopologicalSpace X]
    [NormedAddCommGroup E] [NormedSpace ℝ E]
    {N S : Set X} (hSN : S ⊆ N)
    (G : OpenPartialHomeomorph X E) (a b : E →ᴬ[ℝ] ℝ) (v : E)
    (hav : a.contLinear v = 0) (hbv : b.contLinear v = 1)
    (hN : ∀ y ∈ G.source, y ∈ N ↔ 0 ≤ a (G y) ∧ 0 ≤ b (G y))
    (hS : ∀ y ∈ G.source, y ∈ S ↔ b (G y) = 0 ∧ 0 ≤ a (G y))
    (x : S) (hx : (x : X) ∈ G.source) :
    ∃ c : OpenPartialHomeomorph (S × Ico (0 : ℝ) 1) N,
      collarBase x ∈ c.source ∧
        ∀ y, collarBase y ∈ c.source → c (collarBase y) = Set.inclusion hSN y := by
  have haddA (z : E) (t : ℝ) : a (z + t • v) = a z := by
    simpa only [vadd_eq_add, map_smul, hav, smul_zero, zero_vadd, zero_add, add_comm]
      using a.map_vadd z (t • v)
  have haddB (z : E) (t : ℝ) : b (z + t • v) = b z + t := by
    simpa only [vadd_eq_add, map_smul, hbv, smul_eq_mul, mul_one, add_comm]
      using b.map_vadd z (t • v)
  let project : E → E := fun z => z + (-b z) • v
  have hproject : Continuous project := continuous_id.add (b.continuous.neg.smul continuous_const)
  have hpA (z : E) : a (project z) = a z := haddA z (-b z)
  have hpB (z : E) : b (project z) = 0 := by
    change b (z + (-b z) • v) = 0
    rw [haddB]
    exact add_neg_cancel _
  let f : S × Ico (0 : ℝ) 1 → E := fun z => G z.1 + (z.2 : ℝ) • v
  let A : Set (S × Ico (0 : ℝ) 1) := {z | (z.1 : X) ∈ G.source}
  have hA : IsOpen A := G.open_source.preimage (continuous_subtype_val.comp continuous_fst)
  have hf : ContinuousOn f A :=
    (G.continuousOn.comp (continuous_subtype_val.comp continuous_fst).continuousOn
      (fun _ hz => hz)).add
        ((continuous_subtype_val.comp continuous_snd).smul continuous_const).continuousOn
  let D : TopologicalSpace.Opens (S × Ico (0 : ℝ) 1) :=
    ⟨A ∩ f ⁻¹' G.target, hf.isOpen_inter_preimage hA G.open_target⟩
  let W0 : Set N := (Subtype.val : N → X) ⁻¹' G.source
  have hW0 : IsOpen W0 := G.open_source.preimage continuous_subtype_val
  have hG0 : ContinuousOn (fun y : N => G y) W0 :=
    G.continuousOn.comp continuous_subtype_val.continuousOn (fun _ hy => hy)
  let W1 : Set N := W0 ∩ (fun y : N => project (G y)) ⁻¹' G.target
  have hW1 : IsOpen W1 :=
    (hproject.continuousOn.comp hG0 (mapsTo_univ _ _)).isOpen_inter_preimage hW0 G.open_target
  let W : TopologicalSpace.Opens N :=
    ⟨W1 ∩ (fun y : N => b (G y)) ⁻¹' Iio 1,
      (b.continuous.continuousOn.comp (hG0.mono inter_subset_left)
        (mapsTo_univ _ _)).isOpen_inter_preimage hW1 isOpen_Iio⟩
  have hbaseB (z : S) (hz : (z : X) ∈ G.source) : b (G z) = 0 :=
    ((hS z hz).mp z.property).1
  have hfN (z : D) : G.symm (f z) ∈ N := by
    apply (hN _ (G.map_target z.property.2)).mpr
    rw [G.right_inv z.property.2]
    exact ⟨(haddA _ _).symm ▸ ((hS z.val.1 z.property.1).mp z.val.1.property).2,
      by
        change 0 ≤ b (G z.val.1 + (z.val.2 : ℝ) • v)
        rw [haddB, hbaseB z.val.1 z.property.1, zero_add]
        exact z.val.2.property.1⟩
  have hfW (z : D) : (⟨G.symm (f z), hfN z⟩ : N) ∈ W := by
    have hcoord : G (G.symm (f z)) = f z := G.right_inv z.property.2
    refine ⟨⟨G.map_target z.property.2, ?_⟩, ?_⟩
    · change project (G (G.symm (f z))) ∈ G.target
      rw [hcoord]
      have hp : project (f z) = G z.val.1 := by
        dsimp only [project, f]
        rw [haddB, hbaseB z.val.1 z.property.1, zero_add]
        simp only [neg_smul]
        abel
      rw [hp]
      exact G.map_source z.property.1
    · change b (G (G.symm (f z))) < 1
      rw [hcoord]
      change b (G z.val.1 + (z.val.2 : ℝ) • v) < 1
      rw [haddB, hbaseB z.val.1 z.property.1, zero_add]
      exact z.val.2.property.2
  have hpS (y : W) : G.symm (project (G y.val)) ∈ S := by
    apply (hS _ (G.map_target y.property.1.2)).mpr
    rw [G.right_inv y.property.1.2, hpB, hpA]
    exact ⟨rfl, ((hN y.val y.property.1.1).mp y.val.property).1⟩
  have htI (y : W) : b (G y.val) ∈ Ico (0 : ℝ) 1 :=
    ⟨((hN y.val y.property.1.1).mp y.val.property).2, y.property.2⟩
  have hgD (y : W) :
      (⟨G.symm (project (G y.val)), hpS y⟩, ⟨b (G y.val), htI y⟩) ∈ D := by
    refine ⟨G.map_target y.property.1.2, ?_⟩
    change G (G.symm (project (G y.val))) + b (G y.val) • v ∈ G.target
    rw [G.right_inv y.property.1.2]
    have hp : project (G y.val) + b (G y.val) • v = G y.val := by
      dsimp only [project]
      simp only [neg_smul]
      abel
    rw [hp]
    exact G.map_source y.property.1.1
  let F : D ≃ₜ W :=
    { toFun := fun z => ⟨⟨G.symm (f z), hfN z⟩, hfW z⟩
      invFun := fun y =>
        ⟨(⟨G.symm (project (G y.val)), hpS y⟩, ⟨b (G y.val), htI y⟩), hgD y⟩
      left_inv := by
        intro z
        apply Subtype.ext
        apply Prod.ext
        · apply Subtype.ext
          change G.symm (project (G (G.symm (f z)))) = z.val.1
          rw [G.right_inv z.property.2]
          have hp : project (f z) = G z.val.1 := by
            dsimp only [project, f]
            rw [haddB, hbaseB z.val.1 z.property.1, zero_add]
            simp only [neg_smul]
            abel
          rw [hp, G.left_inv z.property.1]
        · apply Subtype.ext
          change b (G (G.symm (f z))) = (z.val.2 : ℝ)
          rw [G.right_inv z.property.2]
          change b (G z.val.1 + (z.val.2 : ℝ) • v) = _
          rw [haddB, hbaseB z.val.1 z.property.1, zero_add]
      right_inv := by
        intro y
        apply Subtype.ext
        apply Subtype.ext
        change G.symm (G (G.symm (project (G y.val))) + b (G y.val) • v) = y.val
        rw [G.right_inv y.property.1.2]
        have hp : project (G y.val) + b (G y.val) • v = G y.val := by
          dsimp only [project]
          simp only [neg_smul]
          abel
        rw [hp, G.left_inv y.property.1.1]
      continuous_toFun := by
        apply Continuous.subtype_mk
        apply Continuous.subtype_mk
        exact G.symm.continuousOn.comp_continuous
          (hf.comp_continuous continuous_subtype_val (fun z => z.property.1))
          (fun z => z.property.2)
      continuous_invFun := by
        have hGy : Continuous (fun y : W => G y.val) :=
          G.continuousOn.comp_continuous
            (continuous_subtype_val.comp continuous_subtype_val) (fun y => y.property.1.1)
        apply Continuous.subtype_mk
        exact (G.symm.continuousOn.comp_continuous (hproject.comp hGy)
          (fun y => y.property.1.2)).subtype_mk _ |>.prodMk
            ((b.continuous.comp hGy).subtype_mk _) }
  have hxD : collarBase x ∈ D := by
    refine ⟨hx, ?_⟩
    change G x + (0 : ℝ) • v ∈ G.target
    simpa only [zero_smul, add_zero] using G.map_source hx
  let d0 : D := ⟨collarBase x, hxD⟩
  let iD := D.openPartialHomeomorphSubtypeCoe ⟨d0⟩
  let iW := W.openPartialHomeomorphSubtypeCoe ⟨F d0⟩
  let c := iD.symm.trans (F.toOpenPartialHomeomorph.trans iW)
  have hcS : c.source = (D : Set (S × Ico (0 : ℝ) 1)) := by
    simp only [c, OpenPartialHomeomorph.trans_source, OpenPartialHomeomorph.symm_source,
      Homeomorph.toOpenPartialHomeomorph_source,
      show iW.source = univ from rfl, preimage_univ, inter_univ]
    exact D.openPartialHomeomorphSubtypeCoe_target ⟨d0⟩
  refine ⟨c, hcS.symm ▸ hxD, ?_⟩
  intro y hy
  have hyD : collarBase y ∈ D := hcS.subset hy
  let dy : D := ⟨collarBase y, hyD⟩
  have hiD : iD.symm (collarBase y) = dy := iD.left_inv (mem_univ dy)
  apply Subtype.ext
  change ((F (iD.symm (collarBase y))).val : X) = y
  rw [hiD]
  change G.symm (G y + (0 : ℝ) • v) = y
  rw [zero_smul, add_zero]
  exact G.left_inv (show (y : X) ∈ G.source from hyD.1)

theorem exists_local_collar_of_marked_face_chart
    {X E : Type*} [TopologicalSpace X]
    [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
    {N S : Set X} (hSN : S ⊆ N)
    (G : OpenPartialHomeomorph X E) (psi lambda : E →ᴬ[ℝ] ℝ) (w v : E)
    (hpw : psi.contLinear w = 1) (hpv : psi.contLinear v = 0)
    (hlv : lambda.contLinear v = 1)
    (hN : ∀ y ∈ G.source, y ∈ N ↔ 0 ≤ psi (G y))
    (hS : ∀ y ∈ G.source, y ∈ S ↔ psi (G y) = 0 ∧ lambda (G y) ≤ 0)
    (x : S) (hx : (x : X) ∈ G.source) :
    ∃ c : OpenPartialHomeomorph (S × Ico (0 : ℝ) 1) N,
      collarBase x ∈ c.source ∧
        ∀ y, collarBase y ∈ c.source → c (collarBase y) = Set.inclusion hSN y := by
  let w' := w - lambda.contLinear w • v
  have hpw' : psi.contLinear w' = 1 := by
    simp only [w', map_sub, map_smul, hpv, smul_zero, sub_zero, hpw]
  have hlw' : lambda.contLinear w' = 0 := by
    simp only [w', map_sub, map_smul, hlv, smul_eq_mul, mul_one, sub_self]
  obtain ⟨H, _, _, _, _, hquad, _, hface⟩ :=
    psi.exists_corner_straightening lambda w' v hpw' hlw' hpv hlv
  let K := G.transHomeomorph H.symm
  have hKN (y : X) (hy : y ∈ K.source) :
      y ∈ N ↔ 0 ≤ psi (K y) ∧ 0 ≤ lambda (K y) := by
    rw [hN y hy]
    exact (show (0 ≤ psi (H.symm (G y)) ∧ 0 ≤ lambda (H.symm (G y))) ↔
      0 ≤ psi (G y) from by simpa only [H.apply_symm_apply] using hquad (H.symm (G y))).symm
  have hKS (y : X) (hy : y ∈ K.source) :
      y ∈ S ↔ lambda (K y) = 0 ∧ 0 ≤ psi (K y) := by
    rw [hS y hy]
    exact (show (lambda (H.symm (G y)) = 0 ∧ 0 ≤ psi (H.symm (G y))) ↔
      (psi (G y) = 0 ∧ lambda (G y) ≤ 0) from by
        simpa only [H.apply_symm_apply] using hface (H.symm (G y))).symm
  exact exists_local_collar_of_quadrant_chart hSN K psi lambda v hpv hlv hKN hKS x hx

end PoincareConjecture.M76.HamiltonIntervalTorus
