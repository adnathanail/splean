import * as React from 'react'
import { type DiagramData, ZxDiagramElement } from '@adnathanail/zxcc'

// Side-effect: touching the class ensures <zx-diagram> is registered even
// if rollup tree-shakes the named export.
void ZxDiagramElement

interface ZXWidgetProps {
  diagram: DiagramData
  goal?: DiagramData | null
}

const LAYOUT_KEY = 'zx-widget-layout'
type Layout = 'horizontal' | 'vertical' | 'goal_hidden'
const LAYOUTS: Layout[] = ['horizontal', 'vertical', 'goal_hidden']

function isLayout(v: unknown): v is Layout {
  return v === 'horizontal' || v === 'vertical' || v === 'goal_hidden'
}

function usePersistedLayout(): [Layout, (l: Layout) => void] {
  const [layout, setLayoutState] = React.useState<Layout>(() => {
    try {
      const stored = localStorage.getItem(LAYOUT_KEY)
      if (isLayout(stored)) return stored
    } catch {
      /* ignore */
    }
    return 'horizontal'
  })

  React.useEffect(() => {
    const handler = (e: StorageEvent) => {
      if (e.key === LAYOUT_KEY && isLayout(e.newValue)) {
        setLayoutState(e.newValue)
      }
    }
    window.addEventListener('storage', handler)
    return () => window.removeEventListener('storage', handler)
  }, [])

  const setLayout = React.useCallback((l: Layout) => {
    setLayoutState(l)
    try {
      localStorage.setItem(LAYOUT_KEY, l)
    } catch {
      /* ignore */
    }
  }, [])

  return [layout, setLayout]
}

function ZXPanel({ diagram, label }: { diagram: DiagramData; label?: string }) {
  const ref = React.useRef<ZxDiagramElement | null>(null)
  React.useEffect(() => {
    if (ref.current) ref.current.diagram = diagram
  }, [diagram])
  return (
    <div style={{ flex: '1 1 0', minWidth: 0 }}>
      {label && (
        <div style={{ fontFamily: 'monospace', fontWeight: 'bold', marginBottom: 4 }}>{label}</div>
      )}
      {React.createElement('zx-diagram', { ref })}
    </div>
  )
}

export default function ZXDiagram({ diagram, goal }: ZXWidgetProps) {
  const [layout, setLayout] = usePersistedLayout()

  if (!goal) {
    return <ZXPanel diagram={diagram} />
  }

  const nextLayout = LAYOUTS[(LAYOUTS.indexOf(layout) + 1) % LAYOUTS.length]
  const buttonLabel = {
    horizontal: '↕ Stack',
    vertical: '⊘ Hide goal',
    goal_hidden: '↔ Side by side',
  }[layout]

  return (
    <div>
      <div style={{ fontFamily: 'monospace', marginBottom: 4 }}>
        <button
          type="button"
          onClick={() => setLayout(nextLayout)}
          style={{ cursor: 'pointer', fontSize: '12px' }}
        >
          {buttonLabel}
        </button>
      </div>
      {layout === 'goal_hidden' ? (
        <ZXPanel diagram={diagram} />
      ) : (
        <div
          style={{
            display: 'flex',
            flexDirection: layout === 'horizontal' ? 'row' : 'column',
            gap: 16,
            alignItems: layout === 'horizontal' ? 'flex-start' : 'stretch',
          }}
        >
          <ZXPanel diagram={diagram} label="Current" />
          <ZXPanel diagram={goal} label="Goal" />
        </div>
      )}
    </div>
  )
}
