import PoincareConjecture.Proofs.M76.Horizon.Dehn.DoubleArc.OriginalDoubleArcEndpointBlockMap
import PoincareConjecture.Proofs.M76.Horizon.Dehn.DoubleArc.SignedDiamondCoordinateRadii
import PoincareConjecture.Proofs.M76.Horizon.Dehn.DoubleArc.SignedPrismReparametrization

set_option autoImplicit false

open Set Geometry Geometry.SimplicialComplex

namespace PoincareConjecture.M76.Dehn

local notation "V3" => (Fin 3 → ℝ)
local notation "P2" => (ℝ × ℝ)

open Classical in
theorem exists_original_endpoint_block_map_of_joint_map
    {E X ι κ : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [FiniteDimensional ℝ E] [TopologicalSpace X]
    {e : ι → OpenPartialHomeomorph X V3} {R C A : Set X}
    (hAC : A ⊆ interior C) (hAR : A ⊆ R) (hAF : (A ∩ frontier R).Finite)
    (S : Fin 2 → Set X) (K : SimplicialComplex ℝ E) [Fintype K.faces]
    (F : X → E) (hF : Continuous F) (H : C ≃ₜ K.space)
    (hH : ∀ x : C, (H x : E) = F x) (g : E → C)
    (hg : ∀ z : K.space, (g z : X) = (H.symm z : X))
    (hgPL : PolyhedralPLInCharts e (fun z => (g z : X)) K.space)
    (M : κ → SimplicialComplex ℝ E) [∀ i, Fintype (M i).faces]
    (hMK : ∀ i, M i ≤ K)
    (hfull : ∀ i t, t ∈ K.faces → (∀ v ∈ t, v ∈ (M i).vertices) → t ∈ (M i).faces)
    (reg fr arc : κ) (sheet : Fin 2 → κ)
    (hreg : ∀ z ∈ K.space, z ∈ (M reg).space ↔ (g z : X) ∈ R)
    (hfr : ∀ z ∈ K.space, z ∈ (M fr).space ↔ (g z : X) ∈ frontier R)
    (harc : ∀ z ∈ K.space, z ∈ (M arc).space ↔ (g z : X) ∈ A)
    (hsheet : ∀ i z, z ∈ K.space → (z ∈ (M (sheet i)).space ↔ (g z : X) ∈ S i))
    (B : (M arc).vertices → OpenPartialHomeomorph X V3)
    (hB : ∀ p : (M arc).vertices,
      MapsTo (fun z => (g z : X)) (K.closedStar p).space (B p).source ∧
      (K.closedStar p).AffineOnFaces (fun z => B p (g z)) ∧
      (∀ y ∈ (B p).source, y ∈ A ↔ y ∈ R ∧ B p y 0 = 0 ∧ B p y 1 = 0) ∧
      ∀ i y, y ∈ (B p).source → (y ∈ S i ↔ y ∈ R ∧ B p y i.castSucc = 0))
    (s : Finset E) (hs : s ∈ (M arc).faces) (hcard : s.card = 2)
    (v : (M arc).vertices) (hvs : (v : E) ∈ s)
    (hregion : (B v).source ⊆ interior R ∨
      (∀ y ∈ (B v).source, y ∈ R ↔ 0 ≤ B v y 2) ∧
      ∀ y ∈ (B v).source, y ∈ frontier R ↔ B v y 2 = 0)
    (hvFr : (g v : X) ∈ frontier R)
    (G : signedTubeDiamond ≃ₜ (K.barycentricDualBlock s).space)
    (hG : G.IsFinitePL) (eta : Fin 2 → Bool)
    (hQ : ∀ eps delta (x : signedTubeDiamond),
      (x : P2) ∈ signedTubeQuarter eps delta ↔
        (G x : E) ∈ signedCoordinateSector (K.barycentricDualBlock s).space
          (fun i z => B v (g z) i.castSucc) eta eps delta)
    (hcenter : (G ⟨(0, 0),
      signedTubeRadius_subset_diamond 0 false (left_mem_segment ℝ _ _)⟩ : E) = s.centroid ℝ id)
    (bArc : Icc (0 : ℝ) 1 ≃ₜ (M arc).space) (hbArc : bArc.IsFinitePL) :
    let V := K.barycentricDualBlock {(v : E)}
    let D := (M reg).barycentricDualBlock {(v : E)}
    let aligned := (signedTubeDiamondReflection eta).trans G
    ∃ (foot : signedTubeDiamond ≃ₜ ↥(V.space ∩ (M fr).space))
      (α β : Icc (0 : ℝ) 1) (hlt : α < β)
      (hsub : Icc (α : ℝ) (β : ℝ) ⊆ Icc (0 : ℝ) 1) (reverseEnds : Bool),
      let index := fun j : Bool => if reverseEnds then !j else j
      ∃ map : ↥(signedTubeDiamond ×ˢ Icc (α : ℝ) (β : ℝ)) ≃ₜ D.space,
        foot.IsFinitePL ∧ map.IsFinitePL ∧
        (∀ j (x : signedTubeDiamond),
          (map ⟨(x, if j then (β : ℝ) else (α : ℝ)), x.property,
            by cases j <;> simp [show (α : ℝ) ≤ β from hlt.le]⟩ : E) =
              if index j then (aligned x : E) else (foot x : E)) ∧
        (∀ t : Icc (α : ℝ) (β : ℝ),
          (map ⟨((0, 0), t), signedTubeRadius_subset_diamond 0 false
            (left_mem_segment ℝ _ _), t.property⟩ : E) = bArc ⟨t, hsub t.property⟩) ∧
        ∀ eps delta (x : ↥(signedTubeDiamond ×ˢ Icc (α : ℝ) (β : ℝ))),
          (x : P2 × ℝ).1 ∈ signedTubeQuarter eps delta ↔
            (map x : E) ∈ D.space ∩ {z | ∀ i : Fin 2,
              if (![eps, delta] i) then 0 ≤ B v (g z) i.castSucc
                else B v (g z) i.castSucc ≤ 0} := by
  classical
  dsimp only
  let D := (M reg).barycentricDualBlock {(v : E)}
  let J := (K.barycentricDualBlock s).space
  let aligned := (signedTubeDiamondReflection eta).trans G
  let zero : signedTubeDiamond := ⟨(0, 0),
    signedTubeRadius_subset_diamond 0 false (left_mem_segment ℝ _ _)⟩
  have hAligned : aligned.IsFinitePL := signedTubeDiamondReflection_trans_isFinitePL hG eta
  have hAlignedCenter : (aligned zero : E) = s.centroid ℝ id := by
    have hz : signedTubeDiamondReflection eta zero = zero := Subtype.ext (signedTubeReflection_zero eta)
    change (G (signedTubeDiamondReflection eta zero) : E) = _
    rw [hz]
    exact hcenter
  obtain ⟨p, oldJoint, oldEta, oldFoot, α, β, hlt, hsub, reverseEnds,
    halfMap, oldMap, hOldJoint, hOldFoot, hOldMap, hHalf, hKeepHalf, hEnd, hAxis, hMem⟩ :=
    exists_original_endpoint_block_map hAC hAR hAF S K F hF H hH g hg hgPL M hMK hfull
      reg fr arc sheet hreg hfr harc hsheet B hB s hs hcard v hvs hregion hvFr bArc hbArc
  let index := fun j : Bool => if reverseEnds then !j else j
  let oldAlignedFoot := (signedTubeDiamondReflection oldEta).trans oldFoot
  let jointEnd : Bool := !reverseEnds
  have hIndex : index jointEnd = true := by cases reverseEnds <;> rfl
  let jt : Icc (α : ℝ) (β : ℝ) := ⟨if jointEnd then (β : ℝ) else (α : ℝ),
    by cases jointEnd <;> simp [show (α : ℝ) ≤ β from hlt.le]⟩
  have hJointEnd (x : signedTubeDiamond) :
      (oldMap ⟨(x, jt), x.property, jt.property⟩ : E) = oldJoint x := by
    have h := hEnd jointEnd x
    change _ = if index jointEnd then _ else _ at h
    simpa only [hIndex, ↓reduceIte] using h
  obtain ⟨_, _, _, _, _, _, _, hJarc, _⟩ := exists_original_signed_tube_joint_intervals
    hAC hAR hAF S K F hF H hH g hg hgPL M hMK hfull reg fr arc sheet
      hreg hfr harc hsheet B hB s hs hcard
  have hOldCenter : (oldJoint zero : E) = s.centroid ℝ id := by
    apply hJarc.subset
    refine ⟨(oldJoint zero).property, ?_⟩
    rw [← hJointEnd zero, hAxis jt]
    exact (bArc ⟨jt, hsub jt.property⟩).property
  let d : signedTubeDiamond ≃ₜ signedTubeDiamond := aligned.trans oldJoint.symm
  have hd : d.IsFinitePL := hAligned.trans hOldJoint.symm
  have hdValue (x : signedTubeDiamond) : oldJoint (d x) = aligned x := oldJoint.apply_symm_apply _
  have hdZero : d zero = zero := oldJoint.injective
    ((hdValue zero).trans (Subtype.ext (hAlignedCenter.trans hOldCenter.symm)))
  let foot := d.trans oldAlignedFoot
  let map := (signedTubePrismReparametrization d α β).trans oldMap
  have hmap : map.IsFinitePL := (signedTubePrismReparametrization_isFinitePL hd hlt).trans hOldMap
  have hfoot : foot.IsFinitePL := hd.trans hOldFoot
  have hValue (x : ↥(signedTubeDiamond ×ˢ Icc (α : ℝ) (β : ℝ))) :
      (map x : E) = oldMap ⟨(d ⟨(x : P2 × ℝ).1, x.property.1⟩, (x : P2 × ℝ).2),
        (d _).property, x.property.2⟩ := rfl
  refine ⟨foot, α, β, hlt, hsub, reverseEnds, map, hfoot, hmap, ?_, ?_, ?_⟩
  · intro j x
    rw [hValue, hEnd]
    change (if index j then (oldJoint (d x) : E) else (oldAlignedFoot (d x) : E)) = _
    rw [hdValue]
    rfl
  · intro t
    have hp := signedTubePrismReparametrization_center d α β hdZero t
    change (oldMap (signedTubePrismReparametrization d α β _) : E) = _
    rw [hp]
    exact hAxis t
  · intro eps delta x
    let oldEps := signedTubeReindex (oldEta 0) eps
    let oldDelta := signedTubeReindex (oldEta 1) delta
    let cuts := {z | ∀ i : Fin 2,
      if (![eps, delta] i) then 0 ≤ B v (g z) i.castSucc else B v (g z) i.castSucc ≤ 0}
    have hCuts : {z | ∀ i : Fin 2,
        if signedTubeReindex (oldEta i) (![oldEps, oldDelta] i) then
          0 ≤ B v (g z) i.castSucc else B v (g z) i.castSucc ≤ 0} = cuts := by
      ext z
      simp [cuts, Fin.forall_fin_two, oldEps, oldDelta]
      intro _
      rfl
    have hOldMem (y : ↥(signedTubeDiamond ×ˢ Icc (α : ℝ) (β : ℝ))) :
        (y : P2 × ℝ).1 ∈ signedTubeQuarter oldEps oldDelta ↔ (oldMap y : E) ∈ D.space ∩ cuts := by
      have h := hMem oldEps oldDelta y
      rw [hCuts] at h
      exact h
    let xd : signedTubeDiamond := ⟨(x : P2 × ℝ).1, x.property.1⟩
    have hNewD : (aligned xd : E) ∈ D.space := by
      rw [← hdValue, ← hJointEnd]
      exact (oldMap _).property
    have hAtJoint := hOldMem ⟨(d xd, jt), (d xd).property, jt.property⟩
    rw [hJointEnd, hdValue] at hAtJoint
    have hNewQuarter := signedDiamond_reflection_coordinate_quarters J
      (fun i z => B v (g z) i.castSucc) eta G hQ eps delta xd
    have hModel : (xd : P2) ∈ signedTubeQuarter eps delta ↔
        (d xd : P2) ∈ signedTubeQuarter oldEps oldDelta := by
      have hNew : (xd : P2) ∈ signedTubeQuarter eps delta ↔ (aligned xd : E) ∈ cuts := by
        constructor
        · intro hx
          have ht := hNewQuarter.mp hx
          intro i
          fin_cases i
          · exact ht.2.1
          · exact ht.2.2
        · intro hx
          exact hNewQuarter.mpr ⟨(aligned xd).property, hx 0, hx 1⟩
      have hOld : (d xd : P2) ∈ signedTubeQuarter oldEps oldDelta ↔ (aligned xd : E) ∈ cuts := by
        simpa only [mem_inter_iff, hNewD, true_and] using hAtJoint
      exact hNew.trans hOld.symm
    exact hModel.trans (hOldMem
      ⟨(d xd, (x : P2 × ℝ).2), (d xd).property, x.property.2⟩)

end PoincareConjecture.M76.Dehn
