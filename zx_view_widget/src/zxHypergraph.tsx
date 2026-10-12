import { type HypergraphInput, ZxHypergraphElement } from '@adnathanail/zxcc'
import * as React from 'react'
import { IdsButton, usePersistedShowIds } from './shared/showIds'

// Side-effect: touching the class ensures <zx-hypergraph> is registered even
// if rollup tree-shakes the named export.
void ZxHypergraphElement

interface ZXHypergraphProps {
  hypergraph: HypergraphInput
}

/** A hypergraph drawn by `<zx-hypergraph>`, exactly where the input places
 *  each dot. Shares the persisted show-IDs toggle with `ZXDiagram`, where it
 *  shows wire ids under the dots and names beside the blobs. */
export default function ZXHypergraph({ hypergraph }: ZXHypergraphProps) {
  const [showIds, setShowIds] = usePersistedShowIds()
  const ref = React.useRef<ZxHypergraphElement | null>(null)
  React.useEffect(() => {
    if (ref.current) ref.current.hypergraph = hypergraph
  }, [hypergraph])
  React.useEffect(() => {
    if (ref.current) ref.current.showLabels = showIds
  }, [showIds])
  return (
    <div>
      <div style={{ fontFamily: 'monospace', marginBottom: 4 }}>
        <IdsButton showIds={showIds} setShowIds={setShowIds} />
      </div>
      {React.createElement('zx-hypergraph', { ref })}
    </div>
  )
}
