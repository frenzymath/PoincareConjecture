import PoincareConjecture.Proofs.M76.PrimeReduction.BallModelCoordinates
import PoincareConjecture.Proofs.M76.PrimeReduction.BoundaryVertexBand
import PoincareConjecture.Proofs.M76.PrimeReduction.BoundaryVertexDisks
import PoincareConjecture.Proofs.M76.Mathlib.FinitePLDiskPrismExtension

set_option autoImplicit false

open Set Geometry

namespace Geometry.SimplicialComplex

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [FiniteDimensional ℝ E] [DecidableEq E]
  {K L : SimplicialComplex ℝ E} [Fintype K.faces] [Fintype L.faces]
  {T : BoundaryTriangleFibers K L}

local notation "I" => Icc (0 : ℝ) 1
local notation "V3" => (Fin 3 → ℝ)

theorem BoundaryEdgeFamily.exists_vertex_extension (P : BoundaryEdgeFamily T)
    (hLK : L ≤ K) (hLcard : ∀ u ∈ L.faces, u.card ≤ 3)
    (hfull : ∀ u ∈ K.faces, (∀ p ∈ u, p ∈ L.vertices) → u ∈ L.faces)
    {p : E} (hp : p ∈ L.vertices) (B : BoundaryVertexHalfBall K L p) :
    let W := (L.barycentricDualBlock {p}).space
    ∃ H : (W ×ˢ I : Set (E × ℝ)) ≃ₜ (K.barycentricDualBlock {p}).space,
      H.IsFinitePL ∧
      (∀ (x : E) (hx : x ∈ W), (H ⟨(x, 0), ⟨hx, le_rfl, zero_le_one⟩⟩ : E) = x) ∧
      (∀ x : (W ×ˢ I : Set (E × ℝ)), (H x : E) ∈ L.space ↔ (x : E × ℝ).2 = 0) ∧
      (∀ s ∈ L.faces, s.card = 2 → ∀ hps : p ∈ s,
        ∀ (x : E × ℝ) (hx : x ∈ (L.barycentricDualBlock s).space ×ˢ I),
          (H ⟨x, ⟨space_subset_of_le (L.barycentricDualBlock_antitone
            (Finset.singleton_subset_iff.mpr hps)) hx.1, hx.2⟩⟩ : E) = P.map s x) := by
  classical
  let N := (K.barycentricDualBlock {p}).space
  let W := (L.barycentricDualBlock {p}).space
  let Q := ((K.barycentricDualBlock {p}).link p).space
  let q := Q ∩ W
  obtain ⟨hQ, hW⟩ := B.boundary_disks
  let a : V3 ≃L[ℝ] ((ℝ × ℝ) × ℝ) :=
    ContinuousLinearEquiv.ofFinrankEq (by simp [Module.finrank_prod])
  have hN : IsFinitePLBallPair ((ℝ × ℝ) × ℝ) N (Q ∪ W) := B.ball.model_equiv a
  have hout : ((Q ∪ W) \ W).Nonempty := by
    obtain ⟨_, C, _, _, hne, G, _, hGb⟩ := hQ
    obtain ⟨y, hy⟩ := hne
    let z := G.symm ⟨y, interior_subset hy⟩
    refine ⟨z, Or.inl z.property, ?_⟩
    intro hzW
    have hzq : (z : E) ∈ q := ⟨z.property, hzW⟩
    have hfront := (hGb z).mp hzq
    have hval : (G z : ℝ × ℝ) = y := congrArg Subtype.val (G.apply_symm_apply _)
    rw [hval] at hfront
    exact hfront.2 hy
  obtain ⟨f, hf, hi, hins, hzero, hcontact, hkeep⟩ :=
    P.exists_vertex_band hLK hLcard hfull hp
  obtain ⟨H, hH, hH0, hHside, hHb, _⟩ :=
    hN.exists_disk_prism_extension hW subset_union_right hout f hf hi
      (fun x hx => Or.inl (hins hx)) hzero hcontact
  refine ⟨H, hH, hH0, ?_, ?_⟩
  · intro x
    have hNW := K.barycentricDualBlock_space_inter_subcomplex L hLK {p}
    have hmem : (H x : E) ∈ L.space ↔ (H x : E) ∈ W := by
      constructor
      · exact fun h => hNW.subset ⟨(H x).property, h⟩
      · exact fun h => (hNW.symm.subset h).2
    exact hmem.trans (hHb x)
  · intro s hs hc hps x hx
    have hxQ : x.1 ∈ Q := K.boundary_edge_dual_subset_vertex_link L hLK hp hc hps
      (space_subset_of_le (K.barycentricDualBlock_mono_of_subcomplex L hLK s) hx.1)
    have hxW : x.1 ∈ W := space_subset_of_le
      (L.barycentricDualBlock_antitone (Finset.singleton_subset_iff.mpr hps)) hx.1
    exact (hHside x ⟨⟨hxQ, hxW⟩, hx.2⟩).trans (hkeep s hs hc hps x hx)

end Geometry.SimplicialComplex
