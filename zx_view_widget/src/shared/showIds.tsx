import * as React from 'react'

// Shared by every widget bundle. Kept in a subdirectory so that rollup, which
// builds one bundle per top-level file in `dist/`, does not treat it as a widget.

/** One key for every widget, so toggling IDs in one toggles them in all. */
const SHOW_IDS_KEY = 'zx-widget-show-ids'

export function usePersistedShowIds(): [boolean, (v: boolean) => void] {
  const [showIds, setShowIdsState] = React.useState<boolean>(() => {
    try {
      return localStorage.getItem(SHOW_IDS_KEY) === 'true'
    } catch {
      return false
    }
  })

  React.useEffect(() => {
    const handler = (e: StorageEvent) => {
      if (e.key === SHOW_IDS_KEY) setShowIdsState(e.newValue === 'true')
    }
    window.addEventListener('storage', handler)
    return () => window.removeEventListener('storage', handler)
  }, [])

  const setShowIds = React.useCallback((v: boolean) => {
    setShowIdsState(v)
    try {
      localStorage.setItem(SHOW_IDS_KEY, String(v))
    } catch {
      /* ignore */
    }
  }, [])

  return [showIds, setShowIds]
}

export function IdsButton({
  showIds,
  setShowIds,
}: {
  showIds: boolean
  setShowIds: (v: boolean) => void
}) {
  return (
    <button
      type="button"
      onClick={() => setShowIds(!showIds)}
      style={{ cursor: 'pointer', fontSize: '12px' }}
    >
      {showIds ? '# Hide IDs' : '# Show IDs'}
    </button>
  )
}
