import PoincareConjecture.Proofs.M28.Sec10_3_Tube.IntrinsicOpenMetric











set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

open Set
open scoped Manifold ContDiff Topology ENNReal Bundle

universe u

namespace PoincareConjecture.M28

variable {M : Type u} [TopologicalSpace M]
  [ChartedSpace (EuclideanSpace ℝ (Fin 3)) M]
  [IsManifold (𝓡 3) ∞ M]



theorem intrinsicOpenMetric_intrinsicEDist (g : RiemannianMetric 3 M)
    (V : TopologicalSpace.Opens M) {S : Set M} (hSV : S ⊆ (V : Set M))
    (p q : V) :
    intrinsicEDist (intrinsicOpenMetric g V) ((Subtype.val : V → M) ⁻¹' S) p q =
      intrinsicEDist g S (p : M) (q : M) := by
  unfold intrinsicEDist
  apply congrArg sInf
  ext L
  constructor
  · rintro ⟨α, hα, hα0, hα1, hαS, hL⟩
    refine ⟨Subtype.val ∘ α,
      (contMDiff_subtype_val (I := 𝓡 3) (U := V)).comp_contMDiffOn hα,
      congrArg Subtype.val hα0, congrArg Subtype.val hα1, ?_, ?_⟩
    · rintro z ⟨t, ht, rfl⟩
      exact hαS ⟨t, ht, rfl⟩
    · exact hL.trans (intrinsicOpenMetric_pathELength g V zero_le_one hα)
  · rintro ⟨α, hα, hα0, hα1, hαS, hL⟩
    obtain ⟨β, hβ, heq, hlength⟩ :=
      exists_intrinsicOpenMetric_path_lift g V zero_le_one hα
        (fun t ht => hSV (hαS ⟨t, ht, rfl⟩))
    refine ⟨β, hβ, Subtype.ext ((heq (by norm_num)).trans hα0),
      Subtype.ext ((heq (by norm_num)).trans hα1), ?_, hL.trans hlength.symm⟩
    rintro z ⟨t, ht, rfl⟩
    change (Subtype.val ∘ β) t ∈ S
    rw [heq ht]
    exact hαS ⟨t, ht, rfl⟩



theorem intrinsicOpenMetric_intrinsicDiameter (g : RiemannianMetric 3 M)
    (V : TopologicalSpace.Opens M) {S : Set M} (hSV : S ⊆ (V : Set M)) :
    intrinsicDiameter (intrinsicOpenMetric g V) ((Subtype.val : V → M) ⁻¹' S) =
      intrinsicDiameter g S := by
  unfold intrinsicDiameter
  apply congrArg sSup
  ext L
  constructor
  · rintro ⟨⟨p, q⟩, rfl⟩
    refine ⟨(⟨(p : V), p.property⟩, ⟨(q : V), q.property⟩), ?_⟩
    exact (intrinsicOpenMetric_intrinsicEDist g V hSV p q).symm
  · rintro ⟨⟨p, q⟩, rfl⟩
    refine ⟨(⟨⟨(p : M), hSV p.property⟩, p.property⟩,
      ⟨⟨(q : M), hSV q.property⟩, q.property⟩), ?_⟩
    exact intrinsicOpenMetric_intrinsicEDist g V hSV _ _

end PoincareConjecture.M28
