import { render as rtlRender } from '@testing-library/react'
import { beforeEach, expect, test, vi } from 'vitest'

vi.mock('@adnathanail/zxcc', () => ({ ZxDiagramElement: class {} }))

const diagram = {
  nodes: [
    { id: 0, type: 'input' as const, ioId: 0 },
    { id: 1, type: 'spider' as const, color: 'Z' as const, phase: '1/2' },
    { id: 2, type: 'output' as const, ioId: 0 },
  ],
  edges: [
    { src: 0, tgt: 1 },
    { src: 1, tgt: 2 },
  ],
}

beforeEach(() => {
  localStorage.clear()
})

test('single-diagram mode renders one <zx-diagram> with the diagram forwarded', async () => {
  const { default: ZXDiagram } = await import('../zxDiagram')
  const { container } = rtlRender(<ZXDiagram diagram={diagram} />)
  const els = container.querySelectorAll('zx-diagram')
  expect(els).toHaveLength(1)
  expect((els[0] as HTMLElement & { diagram: unknown }).diagram).toBe(diagram)
})

test('goal mode renders two <zx-diagram>s plus a layout toggle', async () => {
  const { default: ZXDiagram } = await import('../zxDiagram')
  const goal = { ...diagram }
  const { container } = rtlRender(<ZXDiagram diagram={diagram} goal={goal} />)
  const els = container.querySelectorAll('zx-diagram')
  expect(els).toHaveLength(2)
  expect((els[0] as HTMLElement & { diagram: unknown }).diagram).toBe(diagram)
  expect((els[1] as HTMLElement & { diagram: unknown }).diagram).toBe(goal)
  expect(container.querySelector('button')).not.toBeNull()
})
