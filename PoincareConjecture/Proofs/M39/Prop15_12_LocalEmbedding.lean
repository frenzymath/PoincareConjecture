import PoincareConjecture.Definitions.Ch15.SurgeryComparison
import PoincareConjecture.Proofs.M39.Prop15_12_PathBounds










set_option autoImplicit false

open scoped Manifold ContDiff Bundle ENNReal Topology

universe u

namespace PoincareConjecture.M39

variable {g₀ : StandardInitialMetric} {K : MetricSurgeryConstants}
  {P : SurgeryParameters} {slice : ℝ → GeneralizedSliceCarrier.{u}}
  {metric : ∀ t, RiemannianMetric 3 (slice t).carrier} {T : ℝ}
  (E : SurgeryEventData g₀ K P slice metric T) (i : Fin E.cap_count)
  (C : SurgerySelectedComponent (slice T))



noncomputable def localChildEmbedding :
    (E.local_result i).output.carrier → C.carrier.carrier :=
  C.inverse ∘ E.local_embed i



theorem inclusion_localChildEmbedding
    (hC : Set.range (E.local_embed i) ⊆ Set.range C.inclusion)
    (x : (E.local_result i).output.carrier) :
    C.inclusion (localChildEmbedding E i C x) = E.local_embed i x := by
  obtain ⟨y, hy⟩ := hC (Set.mem_range_self x)
  change C.inclusion (C.inverse (E.local_embed i x)) = E.local_embed i x
  rw [← hy, C.left_inverse]



theorem localChildEmbedding_smooth
    (hC : Set.range (E.local_embed i) ⊆ Set.range C.inclusion) :
    ContMDiff (𝓡 3) (𝓡 3) ∞ (localChildEmbedding E i C) := by
  apply contMDiffOn_univ.mp
  exact C.inverse_smooth.comp (E.local_embed_smooth i).contMDiffOn
    (fun x _ => hC (Set.mem_range_self x))




theorem localChildEmbedding_metric
    (hC : Set.range (E.local_embed i) ⊆ Set.range C.inclusion)
    (gC : RiemannianMetric 3 C.carrier.carrier)
    (hpull : ∀ x v w, (metric T).inner (C.inclusion x)
      (mfderiv (𝓡 3) (𝓡 3) C.inclusion x v)
      (mfderiv (𝓡 3) (𝓡 3) C.inclusion x w) = gC.inner x v w)
    (x : (E.local_result i).output.carrier) (v w : TangentSpace (𝓡 3) x) :
    gC.inner (localChildEmbedding E i C x)
      (mfderiv (𝓡 3) (𝓡 3) (localChildEmbedding E i C) x v)
      (mfderiv (𝓡 3) (𝓡 3) (localChildEmbedding E i C) x w) =
        (E.local_result i).metric.inner x v w := by
  have heq : C.inclusion ∘ localChildEmbedding E i C = E.local_embed i :=
    funext (inclusion_localChildEmbedding E i C hC)
  calc
    _ = (metric T).inner ((C.inclusion ∘ localChildEmbedding E i C) x)
        (mfderiv (𝓡 3) (𝓡 3) (C.inclusion ∘ localChildEmbedding E i C) x v)
        (mfderiv (𝓡 3) (𝓡 3) (C.inclusion ∘ localChildEmbedding E i C) x w) := by
      rw [mfderiv_comp x (C.inclusion_smooth.mdifferentiable (by simp) _)
        ((localChildEmbedding_smooth E i C hC).mdifferentiable (by simp) x)]
      exact (hpull _ _ _).symm
    _ = _ := by
      rw [heq]
      exact E.local_metric i x v w



theorem localChildEmbedding_edist_le
    (hC : Set.range (E.local_embed i) ⊆ Set.range C.inclusion)
    (gC : RiemannianMetric 3 C.carrier.carrier)
    (hpull : ∀ x v w, (metric T).inner (C.inclusion x)
      (mfderiv (𝓡 3) (𝓡 3) C.inclusion x v)
      (mfderiv (𝓡 3) (𝓡 3) C.inclusion x w) = gC.inner x v w)
    (x y : (E.local_result i).output.carrier) :
    gC.edist (localChildEmbedding E i C x) (localChildEmbedding E i C y) ≤
      (E.local_result i).metric.edist x y := by
  have hb := metric_edist_le_mul_of_pullback (E.local_result i).metric gC
    (C := 1) zero_lt_one (localChildEmbedding_smooth E i C hC)
    (fun z v => by
      rw [localChildEmbedding_metric E i C hC gC hpull]
      simp) x y
  simpa using hb




theorem localChildCollapse_edist_le
    (hC : Set.range (E.local_embed i) ⊆ Set.range C.inclusion)
    (gC : RiemannianMetric 3 C.carrier.carrier)
    (hpull : ∀ x v w, (metric T).inner (C.inclusion x)
      (mfderiv (𝓡 3) (𝓡 3) C.inclusion x v)
      (mfderiv (𝓡 3) (𝓡 3) C.inclusion x w) = gC.inner x v w)
    (x : E.terminal.carrier) (hx : x ∈ (E.necks i).neck.carrier)
    (y : E.terminal.carrier) (hy : y ∈ (E.necks i).neck.carrier) :
    gC.edist (localChildEmbedding E i C ((E.local_result i).collapse x))
      (localChildEmbedding E i C ((E.local_result i).collapse y)) ≤
        intrinsicEDist E.limit_metric (E.necks i).neck.carrier x y :=
  (localChildEmbedding_edist_le E i C hC gC hpull _ _).trans
    ((E.local_result i).distance_decreasing x hx y hy)

end PoincareConjecture.M39
