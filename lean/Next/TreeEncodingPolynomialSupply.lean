import Next.TreeEncodingPolynomial

namespace FixedCore.TreeEncoding

variable {V : Type*}

/-- Actual original vertices with positive prescribed leaf supply. -/
def positiveDemandSites [Fintype V] (c : V → ℕ) : Finset V :=
  Finset.univ.filter (fun v => 0 < c v)

end FixedCore.TreeEncoding
