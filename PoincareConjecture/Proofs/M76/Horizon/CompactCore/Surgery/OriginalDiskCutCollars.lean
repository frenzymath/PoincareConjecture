import PoincareConjecture.Proofs.M76.Rigidity.OriginalDiskCutDomainConstruction









set_option autoImplicit false

open Set Metric Geometry

namespace PoincareConjecture.M76

theorem exists_original_disk_cut_domain_with_collars
    {X ι : Type*} [TopologicalSpace X] [T2Space X]
    {e : ι → OpenPartialHomeomorph X (Fin 3 → ℝ)}
    {R U : Set X} {j : (Fin 2 → ℝ) → X}
    (hR : IsCompact R) (he : PLDomain e R)
    (hj : PolyhedralPLInCharts e j (closedBall 0 1))
    (hemb : Topology.IsEmbedding (fun z : closedBall (0 : Fin 2 → ℝ) 1 => j z))
    (hDR : MapsTo j (closedBall 0 1) R)
    (hproper : ∀ z : closedBall (0 : Fin 2 → ℝ) 1, j z ∈ frontier R ↔
      (z : Fin 2 → ℝ) ∈ sphere 0 1)
    (hU : IsOpen U) (hDU : j '' closedBall 0 1 ⊆ U) :
    ∃ P : OriginalDiskProduct e R j,
      MapsTo P.map (closedBall 0 1 ×ˢ Icc (-1 : ℝ) 1) U ∧
      IsOpen ((Subtype.val : R → X) ⁻¹' P.openStrip) ∧
      PLDomain e P.cutCarrier ∧ IsCompact P.cutCarrier ∧
      interior P.cutCarrier = interior R \ P.closedStrip ∧
      frontier P.cutCarrier = (frontier R \ P.openStrip) ∪ P.endDisks ∧
      P.closedStrip ∩ P.cutCarrier = P.endDisks ∧
      P.closedStrip ∪ P.cutCarrier = R ∧ (interior P.cutCarrier).Nonempty ∧
      ∀ ε : ℝ, 0 < ε → ε ≤ 1 →
        IsOpen ((Subtype.val : R → X) ⁻¹'
          (P.map '' (closedBall 0 1 ×ˢ Ioo (-ε) ε))) ∧
        IsOpen ((Subtype.val : frontier R → X) ⁻¹'
          (P.map '' (sphere 0 1 ×ˢ Ioo (-ε) ε))) := by
  obtain ⟨P, hsmall, hcollars⟩ :=
    exists_small_original_disk_product hR he hj hemb hDR hproper hU hDU
  have hopen : IsOpen ((Subtype.val : R → X) ⁻¹' P.openStrip) :=
    (hcollars (1 / 2) (by norm_num) (by norm_num)).1
  obtain ⟨hc, hi, hf, ho, hu, hn⟩ := P.cut_geometry hR hopen
  exact ⟨P, hsmall, hopen, P.plDomain_cut hR he hopen,
    hc, hi, hf, ho, hu, hn, hcollars⟩

end PoincareConjecture.M76
