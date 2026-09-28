import PoincareConjecture.Proofs.M76.Horizon.PrimeReduction.Reattachment.CocoreFamilyCount
import PoincareConjecture.Proofs.M76.Horizon.PrimeReduction.Reattachment.CocoreContactPullback

set_option autoImplicit false
open Set Geometry
namespace PoincareConjecture.M76
local notation "V3" => (Fin 3 → ℝ)

theorem cocore_section_iUnion
    {X κ : Type*} [TopologicalSpace X]
    (Q : OpenPartialHomeomorph X V3) (J Z : Set V3) (S : κ → Set X) :
    (Q '' ((⋃ i, S i) ∩ Q.source) ∩ J) ∩ Z =
      ⋃ i, (Q '' (S i ∩ Q.source) ∩ J) ∩ Z := by
  simp only [iUnion_inter,image_iUnion]

theorem sphere_family_cocore_decrease
    {X ι κ : Type*} [TopologicalSpace X] [T2Space X] [Finite κ] [DecidableEq κ]
    {e : ι → OpenPartialHomeomorph X V3}
    (S : κ → Set X) (sS : ∀ i, ChartwisePLSphere e (S i))
    (hdis : Pairwise fun i j => Disjoint (S i) (S j)) (j : κ)
    (Q : OpenPartialHomeomorph X V3)
    (hQ : ∀ i, (e i).symm.trans Q ∈ piecewiseAffineGroupoid V3)
    (J : SimplicialComplex ℝ V3) (hJ : J.faces.Finite) (hJQ : J.space ⊆ Q.target)
    (A : V3 →ᴬ[ℝ] ℝ) (t : ℝ)
    (hpres : HasDisjointPolygonPresentation
      ((Q '' ((⋃ i, S i) ∩ Q.source) ∩ J.space) ∩ {x | A x = t}))
    {n : ℕ} (L : Polygon V3 (n + 3))
    (hi : Function.Injective L) (he : L.HasSimplicialEdges)
    (hLS : L.boundary ℝ ⊆ (Q '' (S j ∩ Q.source) ∩ J.space) ∩ {x | A x = t})
    (hrem : IsCompact (((Q '' ((⋃ i, S i) ∩ Q.source) ∩ J.space) ∩ {x | A x = t}) \ L.boundary ℝ))
    (N : Bool → Set X) (sN : ∀ b, ChartwisePLSphere e (N b))
    (hNd : Disjoint (N true) (N false))
    (hNS : ∀ b i, i ≠ j → Disjoint (N b) (S i))
    (hdelete : (N true ∪ N false) ∩ Q.symm '' (Q.target ∩ {x | A x = t}) =
      (S j ∩ Q.symm '' (Q.target ∩ {x | A x = t})) \ Q.symm '' L.boundary ℝ) :
    ∀ b, let S' := Function.update S j (N b)
      HasDisjointPolygonPresentation
        ((Q '' ((⋃ i, S' i) ∩ Q.source) ∩ J.space) ∩ {x | A x = t}) ∧
      Nat.card (ConnectedComponents ↥((Q '' ((⋃ i, S' i) ∩ Q.source) ∩ J.space) ∩ {x | A x = t})) <
        Nat.card (ConnectedComponents ↥((Q '' ((⋃ i, S i) ∩ Q.source) ∩ J.space) ∩ {x | A x = t})) ∧
      ((Q '' ((⋃ i, S' i) ∩ Q.source) ∩ J.space) ∩ {x | A x = t}) ⊆
        ((Q '' ((⋃ i, S i) ∩ Q.source) ∩ J.space) ∩ {x | A x = t}) := by
  let slice (T : Set X) := (Q '' (T ∩ Q.source) ∩ J.space) ∩ {x | A x = t}
  have hclosed {T : Set X} (sT : ChartwisePLSphere e T) : IsClosed (slice T) := by
    obtain ⟨P,hP,hPs,_,_⟩ := sT.exists_finite_chart_carrier Q hQ J hJ hJQ
    change IsClosed ((Q '' (T ∩ Q.source) ∩ J.space) ∩ {x | A x = t})
    rw [← hPs]
    exact (P.isCompact_space_of_finite hP).isClosed.inter (isClosed_eq A.continuous continuous_const)
  have hmem {T : Set X} {x : V3} (hx : x ∈ slice T) : Q.symm x ∈ T := by
    obtain ⟨y,hy,hyx⟩ := hx.1.1
    rw [← hyx,Q.left_inv hy.2]
    exact hy.1
  have hsep {T U : Set X} (hTU : Disjoint T U) : Disjoint (slice T) (slice U) :=
    disjoint_left.mpr (fun _ hx hy => disjoint_left.mp hTU (hmem hx) (hmem hy))
  have hwhole : slice (⋃ i, S i) = ⋃ i, slice (S i) :=
    cocore_section_iUnion Q J.space {x | A x = t} S
  have hdel : slice (N true) ∪ slice (N false) = slice (S j) \ L.boundary ℝ :=
    cocore_section_partition_of_contact_deletion Q hJQ
      (fun _ hx => hJQ (hLS hx).1.2) A t N hdelete
  have hrem' : IsCompact (slice (⋃ i, S i) \ L.boundary ℝ) := hrem
  rw [hwhole] at hrem'
  have hcounts := cocore_family_count_after_circle_exchange (fun i => slice (S i))
    (fun i => hclosed (sS i)) (fun i k hik => hsep (hdis hik)) j
    (hwhole ▸ hpres) L hi he hLS hrem'
    (fun b => slice (N b)) (fun b => hclosed (sN b)) (hsep hNd)
    (fun b i hij => hsep (hNS b i hij)) hdel
  intro b
  have hupdate : slice (⋃ i, Function.update S j (N b) i) =
      ⋃ i, Function.update (fun i => slice (S i)) j (slice (N b)) i := by
    rw [show slice (⋃ i, Function.update S j (N b) i) =
      ⋃ i, slice (Function.update S j (N b) i) from
      cocore_section_iUnion Q J.space {x | A x = t} (Function.update S j (N b))]
    congr 1
    funext i
    by_cases hij : i = j
    · subst i
      simp only [Function.update_self]
    · simp only [Function.update_of_ne hij]
  change HasDisjointPolygonPresentation (slice (⋃ i, Function.update S j (N b) i)) ∧
    Nat.card (ConnectedComponents (slice (⋃ i, Function.update S j (N b) i))) <
      Nat.card (ConnectedComponents (slice (⋃ i, S i))) ∧
    slice (⋃ i, Function.update S j (N b) i) ⊆ slice (⋃ i, S i)
  rw [hupdate,hwhole]
  refine ⟨(hcounts b).1,(hcounts b).2,?_⟩
  intro x hx
  obtain ⟨i,hi⟩ := mem_iUnion.mp hx
  by_cases hij : i = j
  · subst i
    simp only [Function.update_self] at hi
    apply mem_iUnion_of_mem j
    apply (hdel.subset ?_).1
    cases b
    · exact Or.inr hi
    · exact Or.inl hi
  · exact mem_iUnion_of_mem i (by simpa only [Function.update_of_ne hij] using hi)

end PoincareConjecture.M76
