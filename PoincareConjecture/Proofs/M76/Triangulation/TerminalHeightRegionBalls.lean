import PoincareConjecture.Proofs.M76.Triangulation.PLBallActualDiskAttachment
import PoincareConjecture.Proofs.M76.Mathlib.HeightSeparatedSets
import PoincareConjecture.Proofs.M76.Triangulation.AlexanderRegionOpenAttachment
import PoincareConjecture.Proofs.M76.Triangulation.AlexanderRegionCertificates

set_option autoImplicit false

open Set Geometry

namespace Set

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [FiniteDimensional ℝ E]

theorem HasAlexanderRegionBalls.of_height_cut_contact
    {B T s d C : Set E} (A : E → ℝ) {c : ℝ}
    (hdim : Module.finrank ℝ E = 3)
    (hB : IsFinitePLBallPair ((ℝ × ℝ) × ℝ) B (d ∪ (s ∩ {x | A x ≤ c})))
    (hT : IsFinitePLBallPair ((ℝ × ℝ) × ℝ) T (d ∪ (s ∩ {x | c ≤ A x})))
    (hBE : IsFinitePLBallPair ((ℝ × ℝ) × ℝ)
      (frontier (C ×ˢ Icc (-1 : ℝ) 1) \ interior B ×ˢ {1})
      ((d ∪ (s ∩ {x | A x ≤ c})) ×ˢ {(1 : ℝ)}))
    (hTE : IsFinitePLBallPair ((ℝ × ℝ) × ℝ)
      (frontier (C ×ˢ Icc (-1 : ℝ) 1) \ interior T ×ˢ {1})
      ((d ∪ (s ∩ {x | c ≤ A x})) ×ˢ {(1 : ℝ)}))
    (hd : IsFinitePLBallPair (ℝ × ℝ) d (s ∩ {x | A x = c}))
    (hdplane : d ⊆ {x | A x = c}) (hdcontact : d ∩ s = s ∩ {x | A x = c})
    (hBbelow : B ⊆ {x | A x ≤ c}) (hTabove : T ⊆ {x | c ≤ A x})
    (hTcut : T ∩ {x | A x = c} = d)
    (hlower : (s ∩ {x | A x < c}).Nonempty)
    (hupper : (s ∩ {x | c < A x}).Nonempty)
    (hBC : B ⊆ interior C) (hTC : T ⊆ interior C)
    (K : SimplicialComplex ℝ E) (hK : K.faces.Finite)
    (hC : IsCompact C) (hCcv : Convex ℝ C) (hCne : (interior C).Nonempty)
    (hKC : K.space = C) : HasAlexanderRegionBalls s C := by
  let b := s ∩ {x | A x ≤ c}
  let t := s ∩ {x | c ≤ A x}
  let q := s ∩ {x | A x = c}
  have hmodel : Module.finrank ℝ ((ℝ × ℝ) × ℝ) = Module.finrank ℝ E := by
    simp [Module.finrank_prod, hdim]
  have hmodel3 : Module.finrank ℝ ((ℝ × ℝ) × ℝ) = 3 := by
    simp [Module.finrank_prod]
  have hbd : b ∩ d = q := by
    apply Subset.antisymm
    · exact fun _ hx => hdcontact.subset ⟨hx.2, hx.1.1⟩
    · intro x hx
      have hxc : A x = c := hx.2
      exact ⟨⟨hx.1, hxc.le⟩, hd.1 hx⟩
  have htd : t ∩ d = q := by
    apply Subset.antisymm
    · exact fun _ hx => hdcontact.subset ⟨hx.2, hx.1.1⟩
    · intro x hx
      have hxc : A x = c := hx.2
      exact ⟨⟨hx.1, hxc.symm.le⟩, hd.1 hx⟩
  have hB' : IsFinitePLBallPair ((ℝ × ℝ) × ℝ) B (b ∪ d) := by
    simpa only [b, union_comm] using hB
  have hT' : IsFinitePLBallPair ((ℝ × ℝ) × ℝ) T (t ∪ d) := by
    simpa only [t, union_comm] using hT
  have hbout : ((b ∪ d) \ d).Nonempty := by
    obtain ⟨x, hxs, hxc⟩ := hlower
    change A x < c at hxc
    exact ⟨x, Or.inl ⟨hxs, hxc.le⟩, fun hx => hxc.ne (hdplane hx)⟩
  have htout : ((t ∪ d) \ d).Nonempty := by
    obtain ⟨x, hxs, hcx⟩ := hupper
    change c < A x at hcx
    exact ⟨x, Or.inl ⟨hxs, hcx.le⟩, fun hx => hcx.ne' (hdplane hx)⟩
  have hside {R w : Set E}
      (hR : IsFinitePLBallPair ((ℝ × ℝ) × ℝ) R (w ∪ d))
      (hwd : w ∩ d = q) (hout : ((w ∪ d) \ d).Nonempty) :
      IsFinitePLBallPair (ℝ × ℝ) w q := by
    have h := hR.boundary_disk_complement hmodel3 hd subset_union_right hout
    change IsFinitePLBallPair (ℝ × ℝ) ((w ∪ d) \ (d \ q)) q at h
    have hremain : (w ∪ d) \ (d \ q) = w := by
      ext x
      have hwdx : (x ∈ w ∧ x ∈ d) ↔ x ∈ q := Set.ext_iff.mp hwd x
      change ((x ∈ w ∨ x ∈ d) ∧ ¬ (x ∈ d ∧ x ∉ q)) ↔ x ∈ w
      tauto
    rwa [hremain] at h
  have hb := hside hB' hbd hbout
  have ht := hside hT' htd htout
  have hBT : B ∩ T = d := inter_eq_of_height_separation A hBbelow hTabove hTcut
    (subset_union_left.trans hB.1)
  have hclB : closure (interior B) = B := hB'.closure_interior_of_finrank_eq hmodel
  have hclT : closure (interior T) = T := hT'.closure_interior_of_finrank_eq hmodel
  have hBf : frontier (interior B) = b ∪ d := hB'.frontier_interior_of_finrank_eq hmodel
  have hTf : frontier (interior T) = t ∪ d := hT'.frontier_interior_of_finrank_eq hmodel
  have hBcl : IsFinitePLBallPair ((ℝ × ℝ) × ℝ) (closure (interior B)) (b ∪ d) := by
    rwa [hclB]
  have hTcl : IsFinitePLBallPair ((ℝ × ℝ) × ℝ) (closure (interior T)) (t ∪ d) := by
    rwa [hclT]
  have hBE' : IsFinitePLBallPair ((ℝ × ℝ) × ℝ)
      (frontier (C ×ˢ Icc (-1 : ℝ) 1) \ interior B ×ˢ {1}) ((b ∪ d) ×ˢ {(1 : ℝ)}) := by
    simpa only [b, union_comm] using hBE
  have hTE' : IsFinitePLBallPair ((ℝ × ℝ) × ℝ)
      (frontier (C ×ˢ Icc (-1 : ℝ) 1) \ interior T ×ˢ {1}) ((t ∪ d) ×ˢ {(1 : ℝ)}) := by
    simpa only [t, union_comm] using hTE
  have hcover : b ∪ t = s := by
    ext x
    have h := le_total (A x) c
    change ((x ∈ s ∧ A x ≤ c) ∨ (x ∈ s ∧ c ≤ A x)) ↔ x ∈ s
    tauto
  obtain ⟨hconn, hfront, hbody, hext⟩ := alexander_attached_open_region_balls
    hdim hb ht hd hbd htd isOpen_interior isOpen_interior
    (hclB.symm ▸ hBC) (hclT.symm ▸ hTC) hBf hTf
    (by rwa [hclB, hclT]) hBcl hTcl hBE' hTE' K hK hC hCcv hCne hKC
  simp only [hclB, hclT, hcover] at hconn hfront hbody hext
  have hcontain : closure (interior (B ∪ T)) ⊆ interior C :=
    (closure_minimal interior_subset (hB.isCompact.isClosed.union hT.isCompact.isClosed)).trans
      (union_subset hBC hTC)
  exact ⟨interior (B ∪ T), isOpen_interior, hconn, hfront, hcontain, hbody, hext⟩

end Set
